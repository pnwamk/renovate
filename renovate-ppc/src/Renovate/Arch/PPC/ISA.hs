{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Renovate.Arch.PPC.ISA (
  isa,
  assemble,
  disassemble,
  Instruction,
  TargetAddress(..),
  -- * Exceptions
  InstructionDisassemblyFailure(..)
  ) where

import           GHC.Stack ( HasCallStack )

import qualified Control.Monad.Catch as C
import           Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as LB
import           Data.Coerce ( coerce )
import           Data.Int ( Int32 )
import qualified Data.Text.Prettyprint.Doc as PP
import           Data.Word ( Word8, Word64 )
import           Text.Printf ( printf )

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.PPC as MP
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import qualified Dismantle.PPC as D

import qualified Renovate as R

data TargetAddress arch = NoAddress
                        | AbsoluteAddress (R.ConcreteAddress arch)
                        deriving (Eq, Ord)

deriving instance (MM.MemWidth (MM.ArchAddrWidth arch)) => Show (TargetAddress arch)

newtype Instruction a = I { unI :: D.AnnotatedInstruction a }
  deriving (Eq, Show)

type instance R.Instruction (MP.AnyPPC v) = Instruction
type instance R.InstructionAnnotation (MP.AnyPPC v) = TargetAddress (MP.AnyPPC v)
type instance R.RegisterType (MP.AnyPPC v) = Some D.Operand

instance PP.Pretty (Instruction a) where
  pretty = PP.pretty . ppcPrettyInstruction

instance Functor Instruction where
  fmap f (I i) =
    case i of
      D.Instruction opc operands ->
        I (D.Instruction (coerce opc) (FC.fmapFC (\(D.Annotated a o) -> D.Annotated (f a) o) operands))

assemble :: (C.MonadThrow m) => Instruction () -> m B.ByteString
assemble = return . LB.toStrict . D.assembleInstruction . toInst

disassemble :: (C.MonadThrow m) => B.ByteString -> m (Int, Instruction ())
disassemble bs =
  case minsn of
    Just i -> return (bytesConsumed, fromInst i)
    Nothing -> C.throwM (InstructionDisassemblyFailure bs bytesConsumed)
  where
    (bytesConsumed, minsn) = D.disassembleInstruction (LB.fromStrict bs)

data InstructionDisassemblyFailure =
  InstructionDisassemblyFailure B.ByteString Int
  deriving (Show)

instance C.Exception InstructionDisassemblyFailure

-- | An 'ISA' description for PowerPC
--
-- For now, the same description works for both PowerPC 32 and PowerPC 64.
isa :: (MM.MemWidth (MM.ArchAddrWidth arch), R.Instruction arch ~ Instruction, R.InstructionAnnotation arch ~ TargetAddress arch) => R.ISA arch
isa =
  R.ISA { R.isaInstructionSize = ppcInstrSize
        , R.isaPrettyInstruction = ppcPrettyInstruction
        , R.isaMakePadding = ppcMakePadding
        , R.isaMakeRelativeJumpTo = ppcMakeRelativeJumpTo
        , R.isaMaxRelativeJumpSize = ppcMaxRelativeJumpSize
        , R.isaJumpType = ppcJumpType
        , R.isaModifyJumpTarget = ppcModifyJumpTarget
        , R.isaMakeSymbolicJump = ppcMakeSymbolicJump
        , R.isaConcretizeAddresses = ppcConcretizeAddresses
        , R.isaSymbolizeAddresses = ppcSymbolizeAddresses
        }

ppcPrettyInstruction :: Instruction a -> String
ppcPrettyInstruction = show . D.ppInstruction . toInst

-- | All instructions on PowerPC are 4 bytes
ppcInstrSize :: Instruction a -> Word8
ppcInstrSize _ = 4

-- | Make the requested number of bytes of padding instructions (as TRAP
-- instructions).  We can only support numbers of bytes that are multiples of
-- four, as that is the only instruction size on PowerPC.
ppcMakePadding :: (HasCallStack) => Word64 -> [Instruction ()]
ppcMakePadding nBytes
  | leftover == 0 = replicate nInsns (fromInst nopInsn)
  | otherwise = error (printf "Unexpected byte count (%d); PowerPC only supports instruction-sized padding" nBytes)
  where
    (nInsns, leftover) = fromIntegral nBytes `divMod` 4
    nopInsn = D.Instruction D.ATTN D.Nil

-- | Make an unconditional relative jump from the given @srcAddr@ to the
-- @targetAddr@.
ppcMakeRelativeJumpTo :: (MM.MemWidth (MM.ArchAddrWidth arch)) => R.ConcreteAddress arch -> R.ConcreteAddress arch -> [Instruction ()]
ppcMakeRelativeJumpTo srcAddr targetAddr
  | offset `mod` 4 /= 0 =
    error (printf "Unaligned jump with source=%s and target=%s" (show srcAddr) (show targetAddr))
  | offset > fromIntegral ppcMaxRelativeJumpSize =
    error (printf "Jump target is too far away with source=%s and target=%s" (show srcAddr) (show targetAddr))
  | otherwise = [fromInst jumpInstr]
  where
    -- We are limited to 24 + 2 bits of offset, where the low two bits must be zero.
    offset :: Integer
    offset = targetAddr `R.addressDiff` srcAddr

    -- We checked to make sure the low bits are zero with the mod case above.
    -- Now we shift off two of the required zeros.
    shiftedOffset :: Int32
    shiftedOffset = fromIntegral offset `shiftR` 2
    jumpInstr = D.Instruction D.B (D.Directbrtarget (D.BT shiftedOffset) D.:< D.Nil)

-- There are 24 bits of offset in the branch instruction, plus 2 zero bits are
-- added for you at the end -- but it's signed, so lose one bit for that for a
-- total of 25 bits in either direction. We subtract 4 instead of 1 also
-- because of the two zero bits implicitly added to each jump offset.
ppcMaxRelativeJumpSize :: Word64
ppcMaxRelativeJumpSize = bit 25 - 4

ppcMakeSymbolicJump :: (MM.MemWidth (MM.ArchAddrWidth arch), R.Instruction arch ~ Instruction)
                    => R.SymbolicAddress arch
                    -> [R.TaggedInstruction arch (TargetAddress arch)]
ppcMakeSymbolicJump symAddr = [R.tagInstruction (Just symAddr) i]
  where
    -- The jump has an invalid destination because it is just a stand-in; it
    -- will be rewritten with a real jump target when we concretize the
    -- instruction.
    jmp = D.Instruction D.B (D.Directbrtarget (D.BT 0) D.:< D.Nil)
    i = annotateInstr (fromInst jmp) NoAddress

-- | This function converts symbolic address references in operands back to
-- concrete values.  As with 'ppcSymbolizeAddresses', it is a no-op on PowerPC.
ppcConcretizeAddresses :: (MM.MemWidth (MM.ArchAddrWidth arch))
                       => MM.Memory (MM.ArchAddrWidth arch)
                       -> R.ConcreteAddress arch
                       -> Instruction (TargetAddress arch) -> Instruction ()
ppcConcretizeAddresses _mem _addr i =
  case unI i of
    D.Instruction opc operands ->
      I (D.Instruction (coerce opc) (FC.fmapFC (\(D.Annotated _ operand) -> D.Annotated () operand) operands))

-- | This function records the real addresses of IP-relative addressing operands.
--
-- In PowerPC, there are no IP-relative addressing operands (besides jumps), so
-- this is a no-op.  Jumps are handled separately (via the 'TaggedInstruction'
-- wrapper).  Since the 'TaggedInstruction' doesn't need to modify the
-- instruction, it can actually be generated in an architecture-independent way
-- (i.e., not in an architecture-specific backend).
--
-- We rewrite all conditional branches into the sequence described in Note
-- [Conditional Branch Restrictions] to allow us flexibility in code layout.
-- Unconditional branches are left alone (though they are tagged with a symbolic
-- address, if requested).
--
-- Note that the long unconditional jump we add has a dummy target, as the real
-- target is specified through the symbolic target.
ppcSymbolizeAddresses :: (MM.MemWidth (MM.ArchAddrWidth arch), R.Instruction arch ~ Instruction)
                      => MM.Memory (MM.ArchAddrWidth arch)
                      -> (R.ConcreteAddress arch -> Maybe (R.SymbolicAddress arch))
                      -> R.ConcreteAddress arch
                      -> Maybe (R.SymbolicAddress arch)
                      -> Instruction ()
                      -> [R.TaggedInstruction arch (TargetAddress arch)]
ppcSymbolizeAddresses _mem _lookupSymAddr _insnAddr mSymbolicTarget i = case unI i of
  D.Instruction opc operands ->
    let newInsn = D.Instruction (coerce opc) (FC.fmapFC annotateNull operands)
    in [R.tagInstruction mSymbolicTarget (I newInsn)]
  where
    annotateNull (D.Annotated _ operand) = D.Annotated NoAddress operand

-- | Classify jumps (and determine their targets, where possible)
ppcJumpType :: (HasCallStack, MM.MemWidth (MM.ArchAddrWidth arch))
            => Instruction t
            -> MM.Memory (MM.ArchAddrWidth arch)
            -> R.ConcreteAddress arch
            -> R.JumpType arch
ppcJumpType i _mem insnAddr =
  case toInst i of
    D.Instruction opc operands ->
      case operands of
        D.Calltarget (D.BT offset) D.:< D.Nil ->
          R.DirectCall insnAddr (fromIntegral (offset `shiftL` 2))
        D.Directbrtarget (D.BT offset) D.:< D.Nil ->
          R.RelativeJump R.Unconditional insnAddr (fromIntegral (offset `shiftL` 2))
        -- GBC has an extra argument generalizing to include a branch hint
        D.Condbrtarget (D.CBT offset) D.:< _crbit D.:< _bh D.:< D.Nil ->
          R.RelativeJump R.Conditional insnAddr (fromIntegral (offset `shiftL` 2))
        D.Condbrtarget (D.CBT offset) D.:< _crbit D.:< D.Nil ->
          R.RelativeJump R.Conditional insnAddr (fromIntegral (offset `shiftL` 2))
        D.Condbrtarget (D.CBT offset) D.:< D.Nil ->
          case opc of
            D.BCLalways ->
              R.RelativeJump R.Unconditional insnAddr (fromIntegral (offset `shiftL` 2))
            _ ->
              R.RelativeJump R.Conditional insnAddr (fromIntegral (offset `shiftL` 2))
        D.Absdirectbrtarget (D.ABT addr) D.:< D.Nil ->
          R.AbsoluteJump R.Unconditional (R.concreteFromAbsolute (fromIntegral (addr `shiftL` 2)))
        D.Abscondbrtarget (D.ACBT addr) D.:< D.Nil ->
          R.AbsoluteJump R.Conditional (R.concreteFromAbsolute (fromIntegral (addr `shiftL` 2)))
        D.Abscondbrtarget (D.ACBT addr) D.:< _ D.:< _ D.:< D.Nil ->
          R.AbsoluteJump R.Conditional (R.concreteFromAbsolute (fromIntegral (addr `shiftL` 2)))
        D.Nil ->
          case opc of
            D.BCTR -> R.IndirectJump R.Unconditional
            D.BCTRL -> R.IndirectCall
            D.TRAP -> R.IndirectCall
            -- Conditional branches to link register
            D.BDNZLR -> R.IndirectCall    -- Some kind of conditional return
            D.BDNZLRL -> R.IndirectCall   -- Conditional return and link
            D.BDNZLRLm -> R.IndirectCall
            D.BDNZLRLp -> R.IndirectCall
            D.BDNZLRm -> R.IndirectCall
            D.BDNZLRp -> R.IndirectCall
            D.BDZLR -> R.IndirectCall
            D.BDZLRL -> R.IndirectCall
            D.BDZLRLm -> R.IndirectCall
            D.BDZLRLp -> R.IndirectCall
            D.BDZLRm -> R.IndirectCall
            D.BDZLRp -> R.IndirectCall
            -- Normal return (branch to link register)
            D.BLR -> R.Return R.Unconditional
            D.BLRL -> R.Return R.Unconditional
            _ -> R.NoJump
        (_ D.:< _) ->
          -- In this case, we handle all of the branches that don't need to inspect
          -- operands (because they are indirect)
          case opc of
            -- Conditional branch through the CTR register
            D.BCCTR -> R.IndirectJump R.Conditional
            D.GBCCTR -> R.IndirectJump R.Conditional
            -- This is a call because it is setting the link register and could
            -- return to the next instruction
            D.BCCTRL -> R.IndirectCall
            D.BCL -> R.IndirectCall
            D.GBCL -> R.IndirectCall
            D.GBCCTRL -> R.IndirectCall
            -- Syscall
            D.SC -> R.IndirectCall
            -- Traps
            D.TW -> R.IndirectCall
            D.TWI -> R.IndirectCall
            D.TD -> R.IndirectCall
            D.TDI -> R.IndirectCall
            -- Returns with extra operands
            D.GBCLR -> R.Return R.Conditional
            D.GBCLRL -> R.Return R.Conditional
            _ -> R.NoJump

-- | Given a jump instruction and a new target address, update the jump
-- instruction to target the new address.
--
-- This function also takes the address of the instruction so that it can
-- compute IP-relative jump offsets.
--
-- Note that we add two bits of available space when we compute the new jump
-- offsets; this is because there are two zero bits implicitly concatenated to
-- the right of the jump offset.  'newJumpOffset' checks the alignment
-- requirement and the range.  When we construct the operand, we shift off the
-- two zero bits.
--
-- See Note [Conditional Branch Restrictions]
ppcModifyJumpTarget :: (HasCallStack, MM.MemWidth (MM.ArchAddrWidth arch), R.Instruction arch ~ Instruction)
                    => R.ConcreteAddress arch
                    -- ^ The address of the instruction
                    -> R.ConcreteFallthrough arch ()
                    -- ^ The instruction to modify, with new targets attached
                    -> Maybe [Instruction ()]
ppcModifyJumpTarget srcAddr (R.FallthroughInstruction i tag) =
  case unI i of
    D.Instruction opc operands -> case tag of
      R.FallthroughTag Nothing Nothing -> die "Probable bug: ppcModifyJumpTarget called with no modified jump targets"
      R.FallthroughTag Nothing (Just fallthroughAddr) -> do
        ftB <- b 1 fallthroughAddr
        return [i, ftB]
      R.FallthroughTag (Just targetAddr) Nothing -> do
        off <- absoluteOff 0 targetAddr
        case operands of
          D.Annotated a (D.Calltarget (D.BT _offset)) D.:< D.Nil ->
            Just [I (D.Instruction opc (D.Annotated a (D.Calltarget off) D.:< D.Nil))]
          D.Annotated a (D.Directbrtarget (D.BT _offset)) D.:< D.Nil ->
            Just [I (D.Instruction opc (D.Annotated a (D.Directbrtarget off) D.:< D.Nil))]
          _ -> die "Unexpected unconditional jump in ppcModifyJumpTarget"
      R.FallthroughTag (Just targetAddr) (Just fallthroughAddr) -> case operands of
        D.Annotated a (D.Condbrtarget (D.CBT _offset)) D.:< rest -> case newJumpOffset 16 srcAddr targetAddr of
          Right tgtOff4 -> do
            ftB <- b 2 fallthroughAddr
            -- Why put a nop? Because we have reserved the space for three
            -- instructions, and we want ftB to be a nop in case the
            -- fallthrough block is laid out next.
            --
            -- With a bit more effort, we could consider testing whether that's
            -- the case to choose between [i, nop, nop] and [i, ftB] (thus
            -- getting one extra attn instruction to catch bugs).
            Just
              [ I (D.Instruction opc (D.Annotated a (D.Condbrtarget (D.CBT (tgtOff4 `shiftR` 2))) D.:< rest))
              , nop
              , ftB
              ]
          Left _ -> case rest of
            crbitrc D.:< D.Annotated a' (D.U5imm condition) D.:< D.Nil
              -- Try inverting the condition. Maybe the fallthrough address is
              -- nearby but the target address is far.
              | Just condition' <- negateCondition condition
              , Right ftOff4 <- newJumpOffset 16 srcAddr fallthroughAddr
              -> do
                -- No sense putting a nop and hoping tgtB becomes a nop as we
                -- did above: we know by the time we get to this address that
                -- targetAddr is far away from srcAddr.
                tgtB <- b 1 targetAddr
                Just
                  [ I . D.Instruction opc
                    $    D.Annotated a (D.Condbrtarget (D.CBT (ftOff4 `shiftR` 2)))
                    D.:< crbitrc
                    D.:< D.Annotated a' (D.U5imm condition')
                    D.:< D.Nil
                  , tgtB
                  ]
            _ -> do -- Worst case. Use unconditional branches for everything.
              ftB <- b 1 fallthroughAddr
              tgtB <- b 2 targetAddr
              Just
                [ I (D.Instruction opc (D.Annotated a (D.Condbrtarget (D.CBT 2)) D.:< rest))
                , ftB
                , tgtB
                ]
        D.Annotated a (D.Calltarget _) D.:< D.Nil -> do
          tgtOff <- absoluteOff 0 targetAddr
          ftB <- b 1 fallthroughAddr
          Just
            [ I (D.Instruction opc (D.Annotated a (D.Calltarget tgtOff) D.:< D.Nil))
            , ftB
            ]
        _ -> die "Unexpected conditional jump in ppcModifyJumpTarget"
  where
  die :: String -> a
  die s = error . unlines $
    [ s
    , "Address: " ++ show srcAddr
    , "Instruction: " ++ ppcPrettyInstruction i
    , "Tag: " ++ show tag
    ]
  absoluteOff n addr = case newJumpOffset 26 (R.addressAddOffset srcAddr (4*n)) addr of
    Left err -> die err
    Right off4 -> Just (D.BT (off4 `shiftR` 2))
  b n addr
    | addr == R.addressAddOffset srcAddr (4*(n+1)) = return nop
    | otherwise = (\off -> I (D.Instruction D.B (D.Annotated () (D.Directbrtarget off) D.:< D.Nil))) <$> absoluteOff n addr
  nop = I . D.Instruction D.ORI
    $    D.Annotated () (D.Gprc (D.GPR 0))
    D.:< D.Annotated () (D.U16imm 0)
    D.:< D.Annotated () (D.Gprc (D.GPR 0))
    D.:< D.Nil

  negateCondition w = case map (testBit w) [4,3,2,1,0] of
    [False, False, True , a    , t    ] -> Just (12 + negateBranchHint 2 a t)
    [False, True , True , a    , t    ] -> Just ( 4 + negateBranchHint 2 a t)
    [True , a    , False, False, t    ] -> Just (18 + negateBranchHint 8 a t)
    [True , a    , False, True , t    ] -> Just (16 + negateBranchHint 8 a t)
    _ -> Nothing

  negateBranchHint aBit = f where
    f False _ = 0
    f True False = aBit + 1
    f True True  = aBit

-- | Compute a new jump offset between the @srcAddr@ and @targetAddr@.
--
-- If the new offset exceeds what is reachable with a single branch instruction,
-- call error.  The limit of the branch is specified as @nBits@, which is the
-- number of bits in the immediate field that will hold the offset.  Note that
-- offsets are signed, so the range check has to account for that.
newJumpOffset :: (HasCallStack, MM.MemWidth (MM.ArchAddrWidth arch)) => Int -> R.ConcreteAddress arch -> R.ConcreteAddress arch -> Either String Int32
newJumpOffset nBits srcAddr targetAddr
  | rawOff `mod` 4 /= 0 =
    Left (printf "Invalid alignment for offset between src=%s and target=%s" (show srcAddr) (show targetAddr))
  | rawOff >= 2^(nBits - 1) || rawOff <= negate (2^(nBits - 1)) =
    Left (printf "Jump offset too large between src=%s and target=%s" (show srcAddr) (show targetAddr))
  | otherwise = Right (fromIntegral rawOff)
  where
    rawOff = targetAddr `R.addressDiff` srcAddr

-- | This is an are orphan instance; is there a better place to put it?
instance R.ToGenericInstruction (MP.AnyPPC v) where
  toGenericInstruction   = toInst
  fromGenericInstruction = fromInst


-- | Convert the 'Instruction' wrapper to the base instruction type, dropping
-- annotations. This operation is depricated in favor of
-- 'R.toGenericInstruction'.
--
-- Note that the coercion of the opcode is safe, because the second type
-- parameter is phantom.
toInst :: Instruction a -> D.Instruction
toInst i =
  case unI i of
    D.Instruction opc annotatedOps ->
      D.Instruction (coerce opc) (FC.fmapFC unannotateOpcode annotatedOps)

-- | Convert the base instruction type to the wrapped 'Instruction' with a unit
-- annotation. This operation is depricated in favor of
-- 'R.fromGenericInstruction'.
fromInst :: D.Instruction -> Instruction ()
fromInst i =
  case i of
    D.Instruction opc unannotatedOps ->
      I (D.Instruction (coerce opc) (FC.fmapFC (D.Annotated ()) unannotatedOps))

unannotateOpcode :: D.Annotated a D.Operand tp -> D.Operand tp
unannotateOpcode (D.Annotated _ op) = op

annotateInstr :: Instruction () -> a -> Instruction a
annotateInstr (I i) a =
  case i of
    D.Instruction opc operands ->
      I (D.Instruction (coerce opc) (FC.fmapFC (\(D.Annotated _ op) -> D.Annotated a op) operands))

{- Note [Conditional Branch Restrictions]

On PowerPC, conditional branches only have 16 bits of offset (14 physical, two
implied), which is only enough to jump within a 64kb region.  This isn't enough
for very reasonable binaries, and the rewriter fails when trying to rewrite the
jumps directly.

The fix is to change the code sequence we generate to incorporate some
unconditional jumps, which have 26 bits of offset (24 bits physical) available.

Assume we have the following original instruction sequence where the jump is out
of range for a conditional branch:

#+BEGIN_SRC asm
bdnz cr3,<target>
#+END_SRC

We can rewrite this to do the actual jumping through longer unconditional jumps:

#+BEGIN_SRC asm
bdnz cr3,8
b 8
b <target>
#+END_SRC

There are two cases:

1. We take the conditional branch

   In this case, we skip to the ~b <target>~ instruction, which does an
   unconditional jump with a longer range.

2. We don't take the conditional branch and need to fall through

   In this case, we fall through to a ~b 8~ instruction, which then jumps past
   our jump from case (1) and to the natural fallthrough

-}
