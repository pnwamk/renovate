{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
-- | Internal helpers for the ELF rewriting interface
module Renovate.Config (
  RenovateConfig(..),
  SomeConfig(..),
  TrivialConfigConstraint,
  compose,
  identity,
  nop
  ) where

import qualified Control.Monad.Catch as C
import           Control.Monad.ST ( ST, RealWorld )
import qualified Data.ByteString as B
import           Data.Word ( Word64 )

import qualified Data.ElfEdit as E
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Architecture.Info as MM
import qualified Data.Macaw.CFG as MM

import qualified Renovate.BasicBlock as B
import qualified Renovate.ISA as ISA
import qualified Renovate.Rewrite as RW
import qualified Renovate.Recovery as R

-- | A wrapper around a 'RenovateConfig' that hides parameters and
-- allows us to have collections of configs while capturing the
-- necessary class dictionaries. The 'SomeConfig' is parameterized by
-- a constraint @c@ over the hidden 'RenovateConfig' params, which
-- supports exposing information about the hidden params, or bundling
-- up other functionality via a type class.
data SomeConfig c (b :: * -> *) = forall arch
                  . (B.InstructionConstraints arch,
                     R.ArchBits arch,
                     c arch b)
                  => SomeConfig (NR.NatRepr (MM.ArchAddrWidth arch)) (RenovateConfig arch b)

-- | A trivial constraint for use with 'SomeConfig'.
class TrivialConfigConstraint arch b
instance TrivialConfigConstraint arch b

-- | The configuration required for a run of the binary rewriter.
--
-- The binary rewriter is agnostic to the container format of the binary (e.g.,
-- ELF, COFF, Mach-O).  This configuration contains all of the information
-- necessary to analyze and rewrite a binary.
--
-- Note that there is information encoded in the config for specific binary
-- formats (e.g., ELF), but the core binary rewriter is still architecture
-- agnostic.  Those extra helpers are used by the different binary format
-- backends in the core.
--
-- The type parameters are as follows:
--
-- * @i@ the type of instructions
-- * @a@ the type of annotations carried on operands
-- * @w@ the width of pointers
-- * @arch@ the architecture type tag for the architecture
-- * @b@ the type of analysis results produced by the analysis and passed to the rewriter
data RenovateConfig arch (b :: * -> *) =
  RenovateConfig { rcISA           :: ISA.ISA arch
                 , rcArchInfo      :: MM.ArchitectureInfo arch
                 -- ^ Architecture info for macaw
                 , rcAssembler     :: forall m . (C.MonadThrow m) => B.Instruction arch () -> m B.ByteString
                 , rcDisassembler  :: forall m . (C.MonadThrow m) => B.ByteString -> m (Int, B.Instruction arch ())
                 , rcELFEntryPoints :: E.Elf (MM.ArchAddrWidth arch) -> [MM.MemAddr (MM.ArchAddrWidth arch)]
                 -- ^ Extra entry points that can be discovered from ELF files
                 , rcBlockCallback :: Maybe (MC.ArchSegmentOff arch -> ST RealWorld ())
                 -- ^ A callback called for each discovered block; the argument
                 -- is the address of the discovered block
                 , rcFunctionCallback :: Maybe (Int, MC.ArchSegmentOff arch -> R.BlockInfo arch -> IO ())
                 -- ^ A callback called for each discovered function.  The
                 -- arguments are the address of the discovered function and the
                 -- recovery info (a summary of the information returned by
                 -- macaw).  The 'Int' is the number of iterations before
                 -- calling the function callback.
                 , rcAnalysis      :: ISA.ISA arch -> MM.Memory (MM.ArchAddrWidth arch) -> R.BlockInfo arch -> b arch
                 -- ^ An analysis to run over the code discovered by macaw, generating a summary of type @b@
                 , rcRewriter      :: b arch -> ISA.ISA arch -> MM.Memory (MM.ArchAddrWidth arch) -> B.SymbolicBlock arch -> RW.RewriteM arch (Maybe [B.TaggedInstruction arch (B.InstructionAnnotation arch)])
                 -- ^ A rewriting pass to run over each basic block
                 , rcCodeLayoutBase :: Word64
                 -- ^ The base address to start laying out new code
                 , rcDataLayoutBase :: Word64
                 -- ^ The base address to start laying out new data
                 , rcUpdateSymbolTable :: Bool
                 -- ^ True if the symbol table should be updated; this is a
                 -- temporary measure.  Our current method for updating the
                 -- symbol table does not work for PowerPC, so we don't want to
                 -- do it there.  Long term, we want to figure out how to update
                 -- PowerPC safely.
                 }

-- | Compose a list of instrumentation functions into a single
-- function suitable for use as an argument to 'redirect'
--
-- The instrumentors are applied in order; that order must be
-- carefully chosen, as the instrumentors are not isolated from each
-- other.
compose :: (Monad m)
        => [B.SymbolicBlock arch -> m (Maybe [B.TaggedInstruction arch (B.InstructionAnnotation arch)])]
        -> (B.SymbolicBlock arch -> m (Maybe [B.TaggedInstruction arch (B.InstructionAnnotation arch)]))
compose funcs = go funcs
  where
    go [] b = return $! Just (B.basicBlockInstructions b)
    go (f:fs) b = do
      mb_is <- f b
      case mb_is of
        Just is -> go fs b { B.basicBlockInstructions = is }
        Nothing -> go fs b

-- | An identity rewriter (i.e., a rewriter that makes no changes, but forces
-- everything to be redirected).
identity :: (Monad m) => b -> ISA.ISA arch -> MM.Memory (MM.ArchAddrWidth arch) -> B.SymbolicBlock arch -> m (Maybe [B.TaggedInstruction arch (B.InstructionAnnotation arch)])
identity _ _ _ sb = return $! Just (B.basicBlockInstructions sb)

nop :: Monad m => b -> ISA.ISA arch -> MM.Memory (MM.ArchAddrWidth arch) -> B.SymbolicBlock arch -> m (Maybe [B.TaggedInstruction arch (B.InstructionAnnotation arch)])
nop _ _ _ _ = return Nothing
