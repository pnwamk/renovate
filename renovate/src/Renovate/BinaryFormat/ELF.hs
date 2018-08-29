{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
-- | An interface for manipulating ELF files
--
-- It provides a convenient interface for loading an ELF file,
-- applying a set of transformations to the text section, and
-- reassembling a working ELF file with the results.
--
-- It works by redirecting all of the code in the original text
-- section to rewritten versions in a new section.  It handles
-- creating the new section and fixing up all of the ELF metadata.
module Renovate.BinaryFormat.ELF (
  withElfConfig,
  withMemory,
  rewriteElf,
  analyzeElf,
  riInitialBytes,
  riSmallBlockCount,
  riReusedByteCount,
  riUnrelocatableTerm,
  riEntryPointAddress,
  riSectionBaseAddress,
  riInstrumentationSites,
  riSegmentVirtualAddress,
  riOverwrittenRegions,
  riAppendedSegments,
  riRecoveredBlocks,
  riOriginalTextSize,
  riNewTextSize,
  riIncompleteBlocks,
  riRedirectionDiagnostics,
  riBlockRecoveryDiagnostics,
  riBlockMapping,
  RenovateConfig(..),
  RewriterInfo,
  SomeBlocks(..)
  ) where

import           GHC.Generics ( Generic )

import           Control.Applicative
import           Control.Arrow ( second )
import qualified Control.Lens as L
import           Control.Monad ( guard, when )
import qualified Control.Monad.Catch as C
import qualified Control.Monad.Catch.Pure as P
import qualified Control.Monad.IO.Class as IO
import qualified Control.Monad.State.Strict as S
import           Data.Bits ( Bits, (.|.) )
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C8
import qualified Data.Foldable as F
import qualified Data.Generics.Product as GL
import qualified Data.List as L
import qualified Data.List.NonEmpty as NEL
import qualified Data.Map as Map
import           Data.Maybe ( catMaybes, maybeToList, listToMaybe )
import           Data.Monoid
import qualified Data.Ord as O
import qualified Data.Sequence as Seq
import           Data.Typeable ( Typeable )
import qualified Data.Vector as V
import           Data.Word ( Word16, Word32, Word64 )
import           Text.Printf ( printf )

import           Prelude

import qualified Data.ElfEdit as E
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Memory.ElfLoader as MM
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.NatRepr as NR
import qualified Lang.Crucible.FunctionHandle as C

import qualified Renovate.Address as RA
import qualified Renovate.Analysis.FunctionRecovery as FR
import qualified Renovate.Arch as Arch
import qualified Renovate.BasicBlock as B
import qualified Renovate.BasicBlock.Assemble as BA
import           Renovate.Config
import qualified Renovate.Diagnostic as RD
import qualified Renovate.ISA as ISA
import qualified Renovate.Recovery as R
import qualified Renovate.Redirect as RE
import qualified Renovate.Redirect.Symbolize as RS
import qualified Renovate.Rewrite as RW

import           Debug.Trace
debug :: a -> String -> a
debug = flip trace
-- | The system page alignment (assuming 4k pages)
pageAlignment :: Word32
pageAlignment = 0x1000

-- | Statistics gathered and diagnostics generated during the
-- rewriting phase.
data RewriterInfo arch =
  RewriterInfo { _riSegmentVirtualAddress :: Maybe Word64
               , _riOverwrittenRegions :: [(String, Word64)]
               -- ^ The name of a data region and its length (which is
               -- the number of zero bytes that that replaced it)
               , _riAppendedSegments :: [(E.ElfSegmentType, Word16, Word64, Word64)]
               -- ^ The type of the segment, the index of the segment,
               -- the aligned offset at which it will be placed, the
               -- amount of padding required.
               , _riEntryPointAddress :: Maybe Word64
               , _riSectionBaseAddress :: Maybe Word64
               , _riInitialBytes :: Maybe B.ByteString
               , _riBlockRecoveryDiagnostics :: [RD.Diagnostic]
               , _riRedirectionDiagnostics :: [RD.Diagnostic]
               , _riRecoveredBlocks :: Maybe SomeBlocks
               , _riInstrumentationSites :: [RW.RewriteSite arch]
               , _riELF :: E.Elf (MM.ArchAddrWidth arch)
               , _riSmallBlockCount :: Int
               -- ^ The number of blocks that were too small to rewrite
               , _riReusedByteCount :: Int
               -- ^ The number of bytes re-used in the base program by the compact layout strategy
               , _riUnrelocatableTerm :: Int
               -- ^ The number of blocks that could not be relocated because
               -- they end with an IP-relative jump
               , _riOriginalTextSize :: Int
               -- ^ The number of bytes in the original text section
               , _riNewTextSize :: Int
               -- ^ The number of bytes allocated in the new text section
               , _riIncompleteBlocks :: Int
               -- ^ The number of blocks in incomplete functions
               , _riBlockMapping :: [(RA.ConcreteAddress arch, RA.ConcreteAddress arch)]
               -- ^ A mapping of original block addresses to rewritten block addresses
               }
  deriving (Generic)

data SomeBlocks = forall arch
                . (B.InstructionConstraints arch)
                => SomeBlocks (ISA.ISA arch) [B.ConcreteBlock arch]

-- | Apply an instrumentation pass to the code in an ELF binary,
-- rewriting the binary.
--
-- This will overwrite the original .text section with redirections to
-- a new segment named 'brittle'.
--
-- It applies the correct rewriter config for the architecture
-- specified by the ELF file, if there is an appropriate rewriter
-- configuration.  If not, an error is returned.  The architecture is
-- determined by examining metadata in the ELF file that lists the
-- machine architecture.  Supported architectures are listed in the
-- Renovate.Arch module hierarchy.

withElfConfig :: (C.MonadThrow m)
              => E.SomeElf E.Elf
              -- ^ The ELF file to analyze
              -> [(Arch.Architecture, SomeConfig c b)]
              -> (forall arch . (R.ArchBits arch,
                                  MBL.BinaryLoader arch (E.Elf (MM.ArchAddrWidth arch)),
                                  E.ElfWidthConstraints (MM.ArchAddrWidth arch),
                                  B.InstructionConstraints arch,
                                  c arch b)
                                   => RenovateConfig arch (E.Elf (MM.ArchAddrWidth arch)) b
                                   -> E.Elf (MM.ArchAddrWidth arch)
                                   -> MBL.LoadedBinary arch (E.Elf (MM.ArchAddrWidth arch))
                                   -> m t)
              -> m t
withElfConfig e0 configs k = do
  case (e0, withElf e0 E.elfMachine) of
    (E.Elf32 e, E.EM_PPC) ->
      case lookup Arch.PPC32 configs of
        Nothing -> C.throwM (UnsupportedArchitecture E.EM_PPC)
        Just (SomeConfig nr binRep cfg)
          | Just PC.Refl <- PC.testEquality nr (NR.knownNat @32)
          , Just PC.Refl <- PC.testEquality binRep MBL.Elf32Repr -> do
              MBL.loadBinary loadOpts e >>= k cfg e
          | otherwise -> error ("Invalid NatRepr for PPC32: " ++ show nr)
    (E.Elf32 _, mach) -> C.throwM (UnsupportedArchitecture mach)
    (E.Elf64 e, E.EM_X86_64) ->
      case lookup Arch.X86_64 configs of
        Nothing -> C.throwM (UnsupportedArchitecture E.EM_X86_64)
        Just (SomeConfig nr binRep cfg)
          | Just PC.Refl <- PC.testEquality nr (NR.knownNat @64)
          , Just PC.Refl <- PC.testEquality binRep MBL.Elf64Repr ->
              MBL.loadBinary loadOpts e >>= k cfg e
          | otherwise -> error ("Invalid NatRepr for X86_64: " ++ show nr)
    (E.Elf64 e, E.EM_PPC64) ->
      case lookup Arch.PPC64 configs of
        Nothing -> C.throwM (UnsupportedArchitecture E.EM_PPC64)
        Just (SomeConfig nr binRep cfg)
          | Just PC.Refl <- PC.testEquality nr (NR.knownNat @64)
          , Just PC.Refl <- PC.testEquality binRep MBL.Elf64Repr ->
              MBL.loadBinary loadOpts e >>= k cfg e
          | otherwise -> error ("Invalid NatRepr for PPC64: " ++ show nr)
    (E.Elf64 _, mach) -> C.throwM (UnsupportedArchitecture mach)
  where
    loadOpts = MM.defaultLoadOptions { MM.loadRegionIndex = Just 0 }

-- | Apply a rewriter to an ELF file using the chosen layout strategy.
--
-- The 'RE.LayoutStrategy' determines how rewritten basic blocks will be laid
-- out in the new binary file.  If the rewriter succeeds, it returns a new ELF
-- file and some metadata describing the changes made to the file.  Some of the
-- metadata is provided by rewriter passes in the 'RW.RewriteM' environment.
rewriteElf :: (B.InstructionConstraints arch,
               MBL.BinaryLoader arch binFmt,
               E.ElfWidthConstraints (MM.ArchAddrWidth arch),
               R.ArchBits arch)
           => RenovateConfig arch binFmt b
           -- ^ The configuration for the rewriter
           -> E.Elf (MM.ArchAddrWidth arch)
           -- ^ The ELF file to rewrite
           -> MBL.LoadedBinary arch binFmt
           -- ^ A representation of the contents of memory of the ELF file
           -- (including statically-allocated data)
           -> RE.LayoutStrategy
           -- ^ The layout strategy for blocks in the new binary
           -> IO (E.Elf (MM.ArchAddrWidth arch), b arch, RewriterInfo arch)
rewriteElf cfg e loadedBinary strat = do
    (analysisResult, ri) <- S.runStateT (unElfRewrite act) (emptyRewriterInfo e)
    return (_riELF ri, analysisResult, ri)
  where
    act = do
      let mem = MBL.memoryImage loadedBinary
      -- FIXME: Use the symbol map from the loaded binary (which we still need to add)
      symmap <- withCurrentELF (buildSymbolMap mem)
      doRewrite cfg loadedBinary symmap strat

-- | Run an analysis over an ELF file without performing any rewriting.
analyzeElf :: (B.InstructionConstraints arch,
               MBL.BinaryLoader arch binFmt,
               E.ElfWidthConstraints (MM.ArchAddrWidth arch),
               R.ArchBits arch)
           => RenovateConfig arch binFmt b
           -- ^ The configuration for the analysis
           -> E.Elf (MM.ArchAddrWidth arch)
           -- ^ The ELF file to analyze
           -> MBL.LoadedBinary arch binFmt
           -- ^ A representation of the contents of memory of the ELF file
           -- (including statically-allocated data)
           -> IO (b arch, [RE.Diagnostic])
analyzeElf cfg e loadedBinary = do
    (b, ri) <- S.runStateT (unElfRewrite act) (emptyRewriterInfo e)
    return (b, _riBlockRecoveryDiagnostics ri)
  where
    act = do
      let mem = MBL.memoryImage loadedBinary
      symmap <- withCurrentELF (buildSymbolMap mem)
      doAnalysis cfg loadedBinary symmap

withElf :: E.SomeElf E.Elf -> (forall w . E.Elf w -> a) -> a
withElf e k =
  case e of
    E.Elf32 e32 -> k e32
    E.Elf64 e64 -> k e64

-- | Extract the 'MM.Memory' from an ELF file.
withMemory :: forall w m a arch
            . (C.MonadThrow m, MM.MemWidth w, Integral (E.ElfWordType w),
               w ~ MM.ArchAddrWidth arch,
               MBL.BinaryLoader arch (E.Elf w))
           => E.Elf w
           -> (MBL.LoadedBinary arch (E.Elf w) -> m a)
           -> m a
withMemory e k = do
  MBL.loadBinary loadOpts e >>= k
  where
    loadOpts = MM.defaultLoadOptions { MM.loadRegionIndex = Just 0 }

findTextSection :: (w ~ MM.ArchAddrWidth arch) => E.Elf w -> ElfRewriter arch (E.ElfSection (E.ElfWordType w))
findTextSection e = do
  case E.findSectionByName (C8.pack ".text") e of
    [textSection] -> return textSection
    [] -> C.throwM NoTextSectionFound
    sections -> C.throwM (MultipleTextSectionsFound (length sections))

-- | Call the given continuation with the current ELF file
--
-- The intention is that functions that simply *read* the current ELF file are
-- wrapped in this combinator as a marker that they are read-only.  Functions
-- that modify the current ELF file will be wrapped in 'modifyCurrentELF'.
withCurrentELF :: (w ~ MM.ArchAddrWidth arch) => (E.Elf w -> ElfRewriter arch a) -> ElfRewriter arch a
withCurrentELF k = do
  elf <- S.gets _riELF
  k elf

-- | A wrapper around functions that modify the current ELF file.
--
-- The modification function can return some extra data if desired.  The idea is that this is a signal that
-- a function mutates the ELF file.
--
-- This should be the only function that writes to the current ELF file
modifyCurrentELF :: (w ~ MM.ArchAddrWidth arch) => (E.Elf w -> ElfRewriter arch (a, E.Elf w)) -> ElfRewriter arch a
modifyCurrentELF k = do
  elf <- S.gets _riELF
  (res, elf') <- k elf
  S.modify' $ \s -> s { _riELF = elf' }
  return res


-- | The rewriter driver
--
-- Constraints:
--
-- * We cannot move code or data
-- * We cannot change the PHDR table (i.e., we cannot add or remove segments)
doRewrite :: (B.InstructionConstraints arch,
              MBL.BinaryLoader arch binFmt,
              E.ElfWidthConstraints (MM.ArchAddrWidth arch),
              R.ArchBits arch)
          => RenovateConfig arch binFmt b
          -> MBL.LoadedBinary arch binFmt
          -> RE.SymbolMap arch
          -> RE.LayoutStrategy
          -> ElfRewriter arch (b arch)
doRewrite cfg loadedBinary symmap strat = do
  -- We pull some information from the unmodified initial binary: the text
  -- section, the entry point(s), and original symbol table (if any).
  textSection <- withCurrentELF findTextSection
  mBaseSymtab <- withCurrentELF getBaseSymbolTable

  -- Remove (and pad out) the sections whose size could change if we
  -- modify the binary.  We'll re-add them later (see @appendHeaders@).
  --
  -- This modifies the underlying ELF file
  modifyCurrentELF padDynamicDataRegions

  -- We need to compute the address to start laying out new code.  We place new
  -- code directly after the old, but that is at the end of the *loadable
  -- segment* containing .text, rather than directly after .text.  There can be
  -- a number of sections directly after .text (e.g., .fini, .rodata,
  -- .eh_frame_hdr, .eh_frame, and probably others), so the safest thing to do
  -- is figure out the next address after the end of the containing segment.
  (newTextAddr, lastTextSecId) <- withCurrentELF getNewTextAddress
--  traceM $ printf "Extra text section layout address is 0x%x" (fromIntegral nextSegmentAddress :: Word64)
  riSegmentVirtualAddress L..= Just (fromIntegral newTextAddr)

  -- Similarly, we need to find space to put new data.  Again, we can't just put
  -- new data directly after or before the actual .data section, as there are a
  -- number of things that come before and after it.  We can't put anything
  -- after .data, as .bss has to be the last section in the last segment.  This
  -- means that we have to find the segment containing .data and use the start
  -- address of the segment to start laying out new data (growing down, towards
  -- the loadable segment containing .text).

  -- Perform the brittle transformation
  --
  -- This computes the new contents of the .text section
  -- (overwrittenBytes) and the contents of the new code segment
  -- (instrumentedBytes), which will be placed at the address computed
  -- above.
  let layoutAddr = RA.concreteFromAbsolute (fromIntegral newTextAddr)
      -- FIXME: This is wrong; it doesn't account for the required alignment we
      -- need.  That is a big challenge because it depends on how much code we
      -- generate.  Maybe we can do something with congruence where we waste up
      -- to a page of space to maintain alignment.
      dataAddr = RA.concreteFromAbsolute (fromIntegral (rcDataLayoutBase cfg))
      textSectionStartAddr = RA.concreteFromAbsolute (fromIntegral (E.elfSectionAddr textSection))
      textSectionEndAddr = RA.addressAddOffset textSectionStartAddr (fromIntegral ((E.elfSectionSize textSection)))

  ( analysisResult
    , overwrittenBytes
    , instrumentedBytes
    , mNewData
    , newSyms ) <- instrumentTextSection cfg loadedBinary textSectionStartAddr textSectionEndAddr
                                       (E.elfSectionData textSection) strat layoutAddr dataAddr symmap

  riOriginalTextSize L..= fromIntegral (B.length overwrittenBytes)
  riNewTextSize L..= fromIntegral (B.length instrumentedBytes)

  -- Since we know where we need to add new data and new text, we can just start
  -- with a fresh ELF file and start copying data over.  As soon as we find a
  -- segment containing .text, we know that we can copy everything over
  -- (recursively), but put our new section after that.
  --
  -- When we get to the point where we want to add our new data section, we'll
  -- have to add some padding before it to maintain alignment of everything
  -- coming after it.


  -- Allocate a new section for the extra bytes of program text we have generated.
  (newTextSecIdx, newTextSec) <- withCurrentELF (newTextSection newTextAddr instrumentedBytes)
  -- Put the new section into the same segment as the actual text section (but
  -- at the end of the segment, after the last section it contains so that we
  -- don't have to move any code around relative to other code).  The start
  -- address was pre-computed to support this layout.
  --
  -- NOTE: We don't update the size of the segment - that size is just advisory,
  -- and we aren't in a great position to compute the real size (since there are
  -- going to be some things in the segment with non-obvious sizes that can't be
  -- computed until layout time).
  let insertAfter sec
        | E.elfSectionIndex sec == lastTextSecId = Seq.fromList [E.ElfDataSection sec, E.ElfDataSection newTextSec]
        | otherwise = Seq.singleton (E.ElfDataSection sec)
  let doAdjustSection e = return ((), e L.& E.elfFileData L.%~ adjustElfSection insertAfter)
  modifyCurrentELF doAdjustSection

  -- Now we need to do another traversal where we fix the alignment of the data
  -- in the data segment.  We have to drop the alignment from 2MB down to
  -- something more reasonable.  We should take the maximum alignment of all of
  -- the sections in the data segment (and then ensure that our choice of
  -- padding works for all of them).  We can then add some raw data at the
  -- beginning of the segment containing the data section.
  --
  -- Later, we will have to perform a further adjustment including adding any
  -- new static data to the beginning of the segment.
  let findSegWithDataSec = return . findSegmentContainingLoadableSection ".data" . F.toList . (L.^. E.elfFileData)
  mDataSeg <- withCurrentELF findSegWithDataSec
  case mDataSeg of
    Nothing -> return ()
    Just dataSeg -> modifyCurrentELF (fixDataAlignment (E.elfSegmentIndex dataSeg) instrumentedBytes)

  case mBaseSymtab of
    Just baseSymtab
      | rcUpdateSymbolTable cfg -> do
          newSymtab <- withCurrentELF (buildNewSymbolTable (E.elfSectionIndex textSection) newTextSecIdx layoutAddr newSyms baseSymtab)
          modifyCurrentELF (appendDataRegion (E.ElfDataSymtab newSymtab))
    _ -> return ()
  modifyCurrentELF appendHeaders

  -- Now overwrite the original code (in the .text segment) with the
  -- content computed by our transformation.
  modifyCurrentELF (overwriteTextSection overwrittenBytes)
  return analysisResult

-- | The analysis driver
doAnalysis :: (B.InstructionConstraints arch,
               MBL.BinaryLoader arch binFmt,
               E.ElfWidthConstraints (MM.ArchAddrWidth arch),
               R.ArchBits arch)
           => RenovateConfig arch binFmt b
           -> MBL.LoadedBinary arch binFmt
           -> RE.SymbolMap arch
           -> ElfRewriter arch (b arch)
doAnalysis cfg loadedBinary symmap = do
  -- We need to compute our instrumentation address *after* we have
  -- removed all of the possibly dynamic sections and ensured that
  -- everything will line up.
  nextSegmentAddress <- withCurrentELF (segmentLayoutAddress (rcCodeLayoutBase cfg))
--  traceM $ printf "Extra text section layout address is 0x%x" (fromIntegral nextSegmentAddress :: Word64)
  riSegmentVirtualAddress L..= Just (fromIntegral nextSegmentAddress)

  analysisResult <- analyzeTextSection cfg loadedBinary symmap
  return analysisResult

buildSymbolMap :: (w ~ MM.ArchAddrWidth arch, Integral (E.ElfWordType w), MM.MemWidth w)
               => MM.Memory w
               -> E.Elf w
               -> ElfRewriter arch (RE.SymbolMap arch)
buildSymbolMap _mem elf = do
  case filter isSymbolTable (F.toList (E._elfFileData elf)) of
    [E.ElfDataSymtab table] -> do
      let entries = catMaybes (map mkPair (F.toList (E.elfSymbolTableEntries table)))
      return (foldr (uncurry Map.insert) mempty entries)
    -- TODO: can there be more than 1 symbol table?
    _ -> return mempty
  where
    mkPair e
      | let addr = RA.concreteFromAbsolute (fromIntegral (E.steValue e))
      , E.steType e == E.STT_FUNC = Just (addr, E.steName e)
      | otherwise = Nothing

isSymbolTable :: E.ElfDataRegion w -> Bool
isSymbolTable (E.ElfDataSymtab{}) = True
isSymbolTable _                   = False

buildNewSymbolTable :: (w ~ MM.ArchAddrWidth arch, E.ElfWidthConstraints w, MM.MemWidth w)
                    => Word16
                    -> E.ElfSectionIndex
                    -> RA.ConcreteAddress arch
                    -> RE.NewSymbolsMap arch
                    -> E.ElfSymbolTable (E.ElfWordType w)
                    -- ^ The original symbol table
                    -> E.Elf w
                    -> ElfRewriter arch (E.ElfSymbolTable (E.ElfWordType w))
buildNewSymbolTable textSecIdx extraTextSecIdx layoutAddr newSyms baseTable elf
  | trace (printf "New symbol table index is %d" (nextSectionIndex elf)) False = undefined
  | otherwise =
  return $ baseTable { E.elfSymbolTableEntries = E.elfSymbolTableEntries baseTable <>
                       newEntries (toMap (E.elfSymbolTableEntries baseTable))
                     , E.elfSymbolTableIndex = nextSectionIndex elf
                     }
  where
    toMap      t = Map.fromList [ (E.steValue e, e) | e <- V.toList t ]
    newEntries t = V.fromList   [ newFromEntry textSecIdx extraTextSecIdx layoutAddr e ca nm
                                | (ca, (oa, nm)) <- Map.toList newSyms
                                , e <- maybeToList $! Map.lookup (fromIntegral (RA.absoluteAddress oa)) t
                                ]

-- | Find the address we want to have our new text section start at
--
-- We need the new text section to live in the same loadable segment as the
-- original text section, since we cannot add new segments.  Our approach in
-- this function is to traverse the top-level segments in the ELF file.  For
-- each segment, see if it contains (recursively) the .text section.  If it
-- does, find the address and size of the last section in the segment and use
-- them to compute the start address of the new text section (which will be
-- placed at the end of the segment).
--
-- Also returns the index of the last section, which is used to identify where
-- to insert the new text section while building a new ELF file.
getNewTextAddress :: ( w ~ MM.ArchAddrWidth arch
                     , Num (E.ElfWordType w)
                     )
                  => E.Elf w
                  -> ElfRewriter arch (E.ElfWordType w, Word16)
getNewTextAddress e =
  case findSegmentContainingLoadableSection ".text" (F.toList (e L.^. E.elfFileData)) of
    Nothing -> C.throwM (NoSectionFound ".text")
    Just seg -> do
      case findLastSection (E.elfSegmentData seg) of
        Nothing -> C.throwM CannotAllocateTextSection
        Just lastSec -> return (E.elfSectionAddr lastSec + E.elfSectionSize lastSec, E.elfSectionIndex lastSec)

-- | Modify an ELF file by mapping sections to a sequence of data regions.
--
-- To leave a section unmodified, create a singleton data region (with 'E.ElfDataSection')
--
-- This function is general enough to support adding sections before or after an
-- existing section, replacing a section, or removing a section.
adjustElfSection :: forall w
                   . (E.ElfSection (E.ElfWordType w) -> Seq.Seq (E.ElfDataRegion w))
                   -- ^ A function to apply to an 'E.ElfSection' that will
                   -- provide the replacement sequence of data (which could be
                   -- sections or other data regions)
                  -> Seq.Seq (E.ElfDataRegion w)
                  -> Seq.Seq (E.ElfDataRegion w)
adjustElfSection f = mconcat . map go . F.toList
  where
    go :: E.ElfDataRegion w -> Seq.Seq (E.ElfDataRegion w)
    go r =
      case r of
        E.ElfDataElfHeader -> Seq.singleton r
        E.ElfDataSegmentHeaders -> Seq.singleton r
        E.ElfDataSectionHeaders -> Seq.singleton r
        E.ElfDataSectionNameTable {} -> Seq.singleton r
        E.ElfDataGOT {} -> Seq.singleton r
        E.ElfDataStrtab {} -> Seq.singleton r
        E.ElfDataSymtab {} -> Seq.singleton r
        E.ElfDataRaw {} -> Seq.singleton r
        E.ElfDataSection sec -> f sec
        E.ElfDataSegment seg ->
          Seq.singleton (E.ElfDataSegment (seg { E.elfSegmentData = adjustElfSection f (E.elfSegmentData seg)}))

-- | Fix the alignment of the given segment given that we are adding @bytes@ before it into the executable
--
-- We want to drop the alignment of the segment to be the maximum of the
-- alignment of any section.  We then need to add a data region (with zeroes) as
-- the first item in the segment to maintain the congruence constraint on
-- segment alignment.
--
-- If we are adding @extra@ bytes of new text to the file (which shifts the
-- offsets of everything else), we need to add
--
-- > align - (extra % align)
--
-- bytes to the start of the data section.
fixDataAlignment :: ( w ~ MM.ArchAddrWidth arch
                    , Integral (E.ElfWordType w)
                    )
                 => E.SegmentIndex
                 -> B.ByteString
                 -> E.Elf w
                 -> ElfRewriter arch ((), E.Elf w)
fixDataAlignment targetSegIdx bytes e0 =
  ((),) <$> E.traverseElfSegments replaceTargetSegment e0
  where
    replaceTargetSegment seg
      | E.elfSegmentIndex seg == targetSegIdx = do
          let maxAlign s b = max b (E.elfSectionAddrAlign s)
          let maxSectionAlign = F.foldr (foldSections maxAlign) 16 (E.elfSegmentData seg)
          let paddingBytes = fromIntegral maxSectionAlign - (B.length bytes `mod` fromIntegral maxSectionAlign)
          let paddingRegion = E.ElfDataRaw (B.replicate paddingBytes 0)
          return seg { E.elfSegmentData = paddingRegion Seq.<| E.elfSegmentData seg
                     , E.elfSegmentAlign = maxSectionAlign
                     }
      | otherwise = return seg

foldSections :: (E.ElfSection (E.ElfWordType w) -> a -> a)
             -> E.ElfDataRegion w
             -> a
             -> a
foldSections f r seed =
  case r of
    E.ElfDataElfHeader -> seed
    E.ElfDataSegmentHeaders -> seed
    E.ElfDataSegment seg -> F.foldr (foldSections f) seed (E.elfSegmentData seg)
    E.ElfDataSectionHeaders -> seed
    E.ElfDataSectionNameTable {} -> seed
    E.ElfDataGOT {} -> seed
    E.ElfDataStrtab {} -> seed
    E.ElfDataSymtab {} -> seed
    E.ElfDataSection sec -> f sec seed
    E.ElfDataRaw {} -> seed

-- | Traverse a segment and return the (physically) last section in the segment
--
-- If the last thing in the segment is not a section, fail.
findLastSection :: Seq.Seq (E.ElfDataRegion w) -> Maybe (E.ElfSection (E.ElfWordType w))
findLastSection = F.foldr go Nothing
  where
    go r msec =
      case r of
        E.ElfDataElfHeader -> Nothing
        E.ElfDataSegmentHeaders -> Nothing
        E.ElfDataSegment seg' -> findLastSection (E.elfSegmentData seg')
        E.ElfDataSectionHeaders -> Nothing
        E.ElfDataSectionNameTable {} -> Nothing
        E.ElfDataGOT {} -> Nothing
        E.ElfDataStrtab {} -> Nothing
        E.ElfDataSymtab {} -> Nothing
        E.ElfDataSection sec -> Just sec
        E.ElfDataRaw {} -> Nothing

findSegmentContainingLoadableSection :: B.ByteString
                                     -> [E.ElfDataRegion w]
                                     -> Maybe (E.ElfSegment w)
findSegmentContainingLoadableSection secName regions =
  case regions of
    [] -> Nothing
    (r:rs) ->
      case r of
        E.ElfDataElfHeader -> findSegmentContainingLoadableSection secName rs
        E.ElfDataSegmentHeaders -> findSegmentContainingLoadableSection secName rs
        E.ElfDataSectionHeaders -> findSegmentContainingLoadableSection secName rs
        E.ElfDataSectionNameTable {} -> findSegmentContainingLoadableSection secName rs
        E.ElfDataGOT {} -> findSegmentContainingLoadableSection secName rs
        E.ElfDataStrtab {} -> findSegmentContainingLoadableSection secName rs
        E.ElfDataSymtab {} -> findSegmentContainingLoadableSection secName rs
        E.ElfDataSection {} -> findSegmentContainingLoadableSection secName rs
        E.ElfDataRaw {} -> findSegmentContainingLoadableSection secName rs
        E.ElfDataSegment seg
          | Just _ <- segmentContains secName seg -> Just seg
          | otherwise -> findSegmentContainingLoadableSection secName rs

segmentContains :: B.ByteString -> E.ElfSegment w -> Maybe (E.ElfSegment w)
segmentContains secName seg =
  segmentForSection Nothing (Just seg) (F.toList (E.elfSegmentData seg))
  where
    segmentForSection :: a -> a -> [E.ElfDataRegion w] -> a
    segmentForSection notFound _ [] = notFound
    segmentForSection notFound onFound (dr:drs) =
      case dr of
        E.ElfDataElfHeader -> segmentForSection notFound onFound drs
        E.ElfDataSegmentHeaders -> segmentForSection notFound onFound drs
        E.ElfDataSectionHeaders -> segmentForSection notFound onFound drs
        E.ElfDataSectionNameTable {} -> segmentForSection notFound onFound drs
        E.ElfDataGOT {} -> segmentForSection notFound onFound drs
        E.ElfDataStrtab {} -> segmentForSection notFound onFound drs
        E.ElfDataSymtab {} -> segmentForSection notFound onFound drs
        E.ElfDataSection sec
          | secName == E.elfSectionName sec -> onFound
          | otherwise -> segmentForSection notFound onFound drs
        E.ElfDataRaw {} -> segmentForSection notFound onFound drs
        E.ElfDataSegment seg'
          | Just _ <- segmentContains secName seg' -> onFound
          | otherwise -> segmentForSection notFound onFound drs


-- | Get the current symbol table
getBaseSymbolTable :: (w ~ MM.ArchAddrWidth arch)
                   => E.Elf w
                   -> ElfRewriter arch (Maybe (E.ElfSymbolTable (E.ElfWordType w)))
getBaseSymbolTable = return . listToMaybe . E.elfSymtab

newFromEntry :: (w ~ MM.ArchAddrWidth arch, MM.MemWidth w, E.ElfWidthConstraints w)
             => Word16
             -> E.ElfSectionIndex
             -> RA.ConcreteAddress arch
             -> E.ElfSymbolTableEntry (E.ElfWordType w)
             -> RA.ConcreteAddress arch
             -> B.ByteString
             -> E.ElfSymbolTableEntry (E.ElfWordType w)
newFromEntry textSecIdx extraTextSecIdx layoutAddr e addr nm = e
  { E.steName  = "__embrittled_" `B.append` nm
  , E.steValue = fromIntegral absAddr
  , E.steIndex = if absAddr >= RA.absoluteAddress layoutAddr
                 then extraTextSecIdx
                 else E.ElfSectionIndex textSecIdx
  }
  where
    absAddr = RA.absoluteAddress addr

-- | Replace all of the dynamically-sized data regions in the ELF file with padding.
--
-- By dynamically-sized, we mean sections whose sizes will change if
-- we add a new section or segment.  These sections are the section
-- and segment tables, the section name table, and the symbol table.
--
-- We replace them with padding so that none of the original contents
-- of the binary need to move.  We will re-create these sections at
-- the end of the binary when we have finished rewriting it.
--
-- NOTE: We are operating under the constraint that we must not add new segments
-- (which would change the size of the program header table), so we do not
-- remove that table.  Also, we believe that the program headers must reside in
-- the first loadable segment.
--
-- NOTE: In elf-edit, the program header table (PHDR) is called
-- 'E.ElfDataSegmentHeaders'
padDynamicDataRegions :: (w ~ MM.ArchAddrWidth arch, Integral (E.ElfWordType w)) => E.Elf w -> ElfRewriter arch ((), E.Elf w)
padDynamicDataRegions e = do
  let layout0 = E.elfLayout e
  ((),) <$> E.traverseElfDataRegions (replaceSectionWithPadding layout0 isDynamicDataRegion) e
  where
    isDynamicDataRegion r =
      case r of
        E.ElfDataSectionHeaders -> True
        E.ElfDataSectionNameTable _ -> True
        E.ElfDataSymtab {} -> True
        E.ElfDataStrtab {} -> True
        _ -> False

appendDataRegion :: (w ~ MM.ArchAddrWidth arch, Ord (E.ElfWordType w), Integral (E.ElfWordType w))
                 => E.ElfDataRegion w
                 -> E.Elf w
                 -> ElfRewriter arch ((), E.Elf w)
appendDataRegion r e = do
  let layout = E.elfLayout e
      sz = E.elfLayoutSize layout
      alignedOffset = fixAlignment sz (fromIntegral pageAlignment)
      paddingBytes = alignedOffset - sz
      paddingRegion = E.ElfDataRaw (B.replicate (fromIntegral paddingBytes) 0)
  let dats = if paddingBytes > 0 then [ paddingRegion, r ] else [ r ]
  return ((), e L.& E.elfFileData L.%~ (`mappend` Seq.fromList dats))

-- | Append the necessary program header data onto the end of the ELF file.
--
-- This includes: section headers, string table, and the section name table.
--
-- NOTE: This explicitly does not include the segment headers, which we strive
-- to not modify.
--
-- NOTE: It also doesn't include the symbol table, since we already put that in
-- place earlier.
appendHeaders :: (w ~ MM.ArchAddrWidth arch, Show (E.ElfWordType w), Bits (E.ElfWordType w), Integral (E.ElfWordType w))
              => E.Elf w
              -> ElfRewriter arch ((), E.Elf w)
appendHeaders elf = do
  let shstrtabidx = nextSectionIndex elf
  let strtabidx = shstrtabidx + 1
--  traceM $ printf "shstrtabidx = %d" shstrtabidx
  let elfData = [ E.ElfDataSectionHeaders
                , E.ElfDataSectionNameTable shstrtabidx
                , E.ElfDataStrtab strtabidx
                ]
  return ((), elf L.& E.elfFileData L.%~ (`mappend` Seq.fromList elfData))

nextSectionIndex :: (Bits (E.ElfWordType s), Show (E.ElfWordType s), Integral (E.ElfWordType s)) => E.Elf s -> Word16
nextSectionIndex e = firstAvailable 0 indexes
  where
    indexes  = Map.keys (E.elfLayout e L.^. E.shdrs)

    firstAvailable ix [] = ix
    firstAvailable ix (next:rest)
      | ix == next = firstAvailable (ix + 1) rest
      | otherwise = ix

replaceSectionWithPadding :: (w ~ MM.ArchAddrWidth arch, Integral (E.ElfWordType w))
                          => E.ElfLayout w
                          -> (E.ElfDataRegion w -> Bool)
                          -> E.ElfDataRegion w
                          -> ElfRewriter arch (E.ElfDataRegion w)
replaceSectionWithPadding layout shouldReplace r
  | not (shouldReplace r) = return r
  | otherwise = do
--      traceM ("Overwriting section " ++ show (elfDataRegionName r))
      riOverwrittenRegions L.%= ((elfDataRegionName r, fromIntegral sz):)
      return (E.ElfDataRaw (B.replicate paddingBytes 0))
  where
    sz = E.elfRegionFileSize layout r
    paddingBytes = fromIntegral sz

elfDataRegionName :: E.ElfDataRegion s -> String
elfDataRegionName r =
  case r of
    E.ElfDataElfHeader        -> "ElfHeader"
    E.ElfDataSegmentHeaders   -> "SegmentHeaders"
    E.ElfDataSegment seg      -> printf "Segment(%s:%d)" (show (E.elfSegmentType seg)) (E.elfSegmentIndex seg)
    E.ElfDataSectionHeaders   -> "SectionHeaders"
    E.ElfDataSectionNameTable _ -> "SectionNameTable"
    E.ElfDataGOT _            -> "GOT"
    E.ElfDataSection sec      -> printf "Section(%s)" (C8.unpack (E.elfSectionName sec))
    E.ElfDataRaw _            -> "RawData"
    E.ElfDataStrtab {}        -> "Strtab"
    E.ElfDataSymtab {}        -> "Symtab"

-- | Find a location that we can put our instrumented code at.
--
-- The key is that we need an address for which we can meet the
-- alignment congruence condition.  We do that by construction.  We
-- choose a base address for the code (the @instrumentationBase@
-- constant defined at the top of the file) and then add in enough
-- padding to the end of the file to bump the address up to the next
-- page boundary.
--
-- When we assemble the final binary, neither the offset nor the
-- virtual address for the segment will be divisible by the executable
-- alignment (0x20000), but they will be congruent (i.e., have the
-- same remainder).
segmentLayoutAddress :: (w ~ MM.ArchAddrWidth arch, Num (E.ElfWordType w), Integral (E.ElfWordType w))
                     => Word64
                     -> E.Elf w
                     -> ElfRewriter arch (E.ElfWordType w)
segmentLayoutAddress segBaseAddr e = do
  let layout = E.elfLayout e
  let totalSize = F.sum $ fmap (E.elfRegionFileSize layout) (L.view E.elfFileData e)
  let addr :: Int
      addr = fromIntegral totalSize
  let aligned = fixAlignment addr (fromIntegral pageAlignment)
  return (fromIntegral segBaseAddr + fromIntegral aligned)

fixAlignment :: Integral w => w -> w -> w
fixAlignment v 0 = v
fixAlignment v 1 = v
fixAlignment v a0
  | m == 0 = c * a
  | otherwise = (c + 1) * a
  where
    a = fromIntegral a0
    (c,m) = v `divMod` a

overwriteTextSection :: (w ~ MM.ArchAddrWidth arch, Integral (E.ElfWordType w)) => B.ByteString -> E.Elf w -> ElfRewriter arch ((), E.Elf w)
overwriteTextSection newBytes e = do
  ((), ) <$> E.elfSections doOverwrite e
  where
    doOverwrite sec
      | E.elfSectionName sec /= C8.pack ".text" = return sec
      | otherwise = do
        when (B.length newBytes /= fromIntegral (E.elfSectionSize sec)) $ do
          C.throwM (RewrittenTextSectionSizeMismatch (B.length newBytes) (fromIntegral (E.elfSectionSize sec)))
        return sec { E.elfSectionData = newBytes
                   , E.elfSectionSize = fromIntegral (B.length newBytes)
                   }

newTextSection :: ( w ~ MM.ArchAddrWidth arch
                  , Num (E.ElfWordType w)
                  , Show (E.ElfWordType w)
                  , Bits (E.ElfWordType w)
                  , Integral (E.ElfWordType w)
                  )
               => E.ElfWordType w
               -> B.ByteString
               -> E.Elf w
               -> ElfRewriter arch (E.ElfSectionIndex, E.ElfSection (E.ElfWordType w))
newTextSection startAddr bytes e = do
  let newTextIdx = nextSectionIndex e
  let sec = E.ElfSection { E.elfSectionName = C8.pack ".brittle"
                         , E.elfSectionType = E.SHT_PROGBITS
                         , E.elfSectionFlags = E.shf_alloc .|. E.shf_execinstr
                         , E.elfSectionAddr = startAddr
                         , E.elfSectionSize = fromIntegral (B.length bytes)
                         , E.elfSectionLink = 0
                         , E.elfSectionInfo = 0
                         , E.elfSectionAddrAlign = 1
                         , E.elfSectionEntSize = 0
                         , E.elfSectionData = bytes
                         , E.elfSectionIndex = newTextIdx
                         }
  return (E.ElfSectionIndex newTextIdx, sec)

-- | Apply the instrumentor to the given section (which should be the
-- .text section), while laying out the instrumented version of the
-- code at the @layoutAddr@.
--
-- The return value is (rewrittenTextSection, instrumentedBytes,
-- newDataSection).  There could be no new data section if none is
-- required.
--
-- Note that the layout of .text section will change exactly what this
-- function does.  We start instrumenting from @main@ (for now) and do
-- not give the instrumentor access to code that comes before @main@
-- in the .text section.  This implies that library code that comes
-- before @main@ will not be instrumented.  We can change that by
-- simply re-arranging the code at link time such that @main@ comes
-- before the library code.
--
-- As a side effect of running the instrumentor, we get information
-- about how much extra space needs to be reserved in a new data
-- section.  The new data section is rooted at @newGlobalBase@.
instrumentTextSection :: forall w arch binFmt b
                       . (w ~ MM.ArchAddrWidth arch,
                          MBL.BinaryLoader arch binFmt,
                          B.InstructionConstraints arch,
                          Integral (E.ElfWordType w),
                          R.ArchBits arch)
                      => RenovateConfig arch binFmt b
                      -> MBL.LoadedBinary arch binFmt
                      -- ^ The memory space
                      -> RA.ConcreteAddress arch
                      -- ^ The address of the start of the text section
                      -> RA.ConcreteAddress arch
                      -- ^ The address of the end of the text section
                      -> B.ByteString
                      -- ^ The bytes of the text section
                      -> RE.LayoutStrategy
                      -- ^ The strategy to use for laying out instrumented blocks
                      -> RA.ConcreteAddress arch
                      -- ^ The address to lay out the instrumented blocks
                      -> RA.ConcreteAddress arch
                      -- ^ The address to lay out the new data section
                      -> RE.SymbolMap arch
                      -- ^ meta data?
                      -> ElfRewriter arch (b arch, B.ByteString, B.ByteString, Maybe B.ByteString, RE.NewSymbolsMap arch)
instrumentTextSection cfg loadedBinary textSectionStartAddr textSectionEndAddr textBytes strat layoutAddr newGlobalBase symmap = do
  withRewriteEnv cfg loadedBinary symmap $ \env -> do
  let isa = rcISA cfg
  let blockInfo = RW.envBlockInfo env
  let blocks = R.biBlocks blockInfo
  let mem = RW.envMemory env
  case cfg of
    -- This pattern match is only here to deal with the existential
    -- quantification inside of RenovateConfig.
    RenovateConfig { rcAnalysis = analysis, rcRewriter = rewriter } -> do
      let (eBaseSymBlocks, r0) = RE.runRewriter isa mem symmap $ do
            RS.symbolizeBasicBlocks (L.sortBy (O.comparing RE.basicBlockAddress) blocks)
      baseSymBlocks <- extractOrThrowRewriterResult eBaseSymBlocks r0
      let symbolicBlockMap = Map.fromList [ (RE.basicBlockAddress cb, sb)
                                          | (cb, sb) <- baseSymBlocks ]
      let analyzeEnv = AnalyzeEnv
            { aeRewriteEnv = env
            , aeSymbolicBlockMap = symbolicBlockMap
            , aeRunRewriteM = RW.runRewriteM env newGlobalBase }
      analysisResult <- IO.liftIO $ analysis analyzeEnv loadedBinary
      let ((eBlocks, r1), info) = RW.runRewriteM env newGlobalBase . RE.resumeRewriterT isa mem symmap r0 $ do
            RE.redirect isa blockInfo textSectionStartAddr textSectionEndAddr (rewriter analysisResult loadedBinary) mem strat layoutAddr baseSymBlocks
      (overwrittenBlocks, instrumentationBlocks) <- extractOrThrowRewriterResult eBlocks r1

      let s1 = RE.rrState r1
      let newSyms = RE.rwsNewSymbolsMap s1
      riRedirectionDiagnostics L..= F.toList (RD.diagnosticMessages $ RE.rrDiagnostics r1)
      riInstrumentationSites L..= RW.infoSites info
      riReusedByteCount L..= RE.rwsReusedByteCount s1
      riSmallBlockCount L..= RE.rwsSmallBlockCount s1
      riUnrelocatableTerm L..= RE.rwsUnrelocatableTerm s1
      riBlockMapping L..= RE.rwsBlockMapping s1
      let allBlocks = overwrittenBlocks ++ instrumentationBlocks
      case cfg of
        RenovateConfig { rcAssembler = asm } -> do
          (overwrittenBytes, instrumentationBytes) <- BA.assembleBlocks mem isa textSectionStartAddr textSectionEndAddr textBytes layoutAddr asm allBlocks
          let newDataBytes = mkNewDataSection newGlobalBase info
          return (analysisResult, overwrittenBytes, instrumentationBytes, newDataBytes, newSyms)

-- | Helper for handling the error case of `RewriterT`.
extractOrThrowRewriterResult :: Either P.SomeException a
                             -> RE.RewriterResult arch
                             -> ElfRewriter arch a
extractOrThrowRewriterResult e r = do
  case e of
    Left exn -> do
      let diagnostics = F.toList (RD.diagnosticMessages $ RE.rrDiagnostics r)
      riRedirectionDiagnostics L..= diagnostics
      C.throwM (RewriterFailure exn diagnostics)
    Right x -> return x

-- | Initialize an 'AnalyzeEnv'.
--
-- This compute the symbolic blocks, which are recomputed in
-- 'instrumentTextSection'. If this is too wasteful we could try
-- caching and reusing.
mkAnalyzeEnv :: B.InstructionConstraints arch
             => RenovateConfig arch binFmt b
             -> RW.RewriteEnv arch
             -> RE.SymbolMap arch
             -> RE.ConcreteAddress arch
             -> ElfRewriter arch (AnalyzeEnv arch)
mkAnalyzeEnv cfg env symmap newGlobalBase = do
  let isa = rcISA cfg
  let mem = RW.envMemory env
  let blocks = R.biBlocks $ RW.envBlockInfo env

  let (eBaseSymBlocks, r) = RE.runRewriter isa mem symmap $
        -- traceM (show (PD.vcat (map PD.pretty (L.sortOn (basicBlockAddress) (F.toList blocks)))))
        RS.symbolizeBasicBlocks (L.sortBy (O.comparing RE.basicBlockAddress) blocks)
  baseSymBlocks <- extractOrThrowRewriterResult eBaseSymBlocks r
  let symbolicBlockMap = Map.fromList [ (RE.basicBlockAddress cb, sb)
                                      | (cb, sb) <- baseSymBlocks ]
  let analyzeEnv = AnalyzeEnv
        { aeRewriteEnv = env
        , aeSymbolicBlockMap = symbolicBlockMap
        , aeRunRewriteM = RW.runRewriteM env newGlobalBase }
  return analyzeEnv

-- | The common code between 'analyzeTextSection' and
-- 'instrumentTextSection' that sets up the 'RewriteEnv'.
withRewriteEnv :: forall w arch binFmt b a
                    . (w ~ MM.ArchAddrWidth arch,
                       MBL.BinaryLoader arch binFmt,
                       B.InstructionConstraints arch,
                       Integral (E.ElfWordType w),
                       R.ArchBits arch)
                   => RenovateConfig arch binFmt b
                   -> MBL.LoadedBinary arch binFmt
                   -- ^ The memory space
                   -> RE.SymbolMap arch
                   -> (RW.RewriteEnv arch -> ElfRewriter arch a)
                   -> ElfRewriter arch a
withRewriteEnv cfg loadedBinary symmap k = do
  let mem = MBL.memoryImage loadedBinary
  -- We use an irrefutable match on the entry point -- we are asserting that the
  -- entry point is mapped in the 'MM.Memory' object passed in.
--  traceM ("analyzeTextSection entry point: " ++ show entryPoint)
--  riEntryPointAddress L..= (fromIntegral <$> MM.msegAddr entryPoint)
  elfEntryPoints@(entryPoint NEL.:| _) <- MBL.entryPoints loadedBinary
  hdlAlloc <- IO.liftIO C.newHandleAllocator
  let isa      = rcISA cfg
      archInfo = rcArchInfo cfg loadedBinary
      recovery = R.Recovery { R.recoveryISA = isa
                            , R.recoveryDis = rcDisassembler cfg
                            , R.recoveryArchInfo = archInfo
                            , R.recoveryHandleAllocator = hdlAlloc
                            , R.recoveryBlockCallback = rcBlockCallback cfg
                            , R.recoveryFuncCallback = fmap (second ($ loadedBinary)) (rcFunctionCallback cfg)
                            }
  blockInfo <- IO.liftIO (R.recoverBlocks recovery mem symmap elfEntryPoints)
  riBlockRecoveryDiagnostics L..= []
  let blocks = R.biBlocks blockInfo
  riRecoveredBlocks L..= Just (SomeBlocks isa blocks)
  let cfgs = FR.recoverFunctions isa mem blockInfo
      Just concEntryPoint = RA.concreteFromSegmentOff mem entryPoint
      env = RW.mkRewriteEnv cfgs concEntryPoint mem blockInfo isa
  k env

analyzeTextSection :: forall w arch binFmt b
                    . (w ~ MM.ArchAddrWidth arch,
                       MBL.BinaryLoader arch binFmt,
                       B.InstructionConstraints arch,
                       Integral (E.ElfWordType w),
                       R.ArchBits arch)
                   => RenovateConfig arch binFmt b
                   -> MBL.LoadedBinary arch binFmt
                   -- ^ The memory space
                   -> RE.SymbolMap arch
                   -> ElfRewriter arch (b arch)
analyzeTextSection cfg loadedBinary symmap = do
  withRewriteEnv cfg loadedBinary symmap $ \env -> do
  -- See "FIXME" comment for 'dataAddr' in 'doRewrite': it says there
  -- that this value is wrong, but I assume we should be wrong the
  -- same way here.
  let newGlobalBase = RA.concreteFromAbsolute (fromIntegral (rcDataLayoutBase cfg))
  analyzeEnv <- mkAnalyzeEnv cfg env symmap newGlobalBase
  IO.liftIO $ rcAnalysis cfg analyzeEnv loadedBinary

mkNewDataSection :: (MM.MemWidth (MM.ArchAddrWidth arch)) => RA.ConcreteAddress arch -> RW.RewriteInfo arch -> Maybe B.ByteString
mkNewDataSection baseAddr info = do
  guard (bytes > 0)
  return (B.pack (replicate bytes 0))
  where
    bytes = fromIntegral (RW.nextGlobalAddress info `RA.addressDiff` baseAddr)

data ElfRewriteException = RewrittenTextSectionSizeMismatch Int Int
                         | StringTableNotFound
                         | BlockRecoveryFailure C.SomeException [RD.Diagnostic]
                         | RewriterFailure C.SomeException [RD.Diagnostic]
                         | UnsupportedArchitecture E.ElfMachine
                         | MemoryLoadError String
                         | NoTextSectionFound
                         | MultipleTextSectionsFound Int
                         | NoSectionFound B.ByteString
                         | CannotAllocateTextSection
                         deriving (Typeable)

deriving instance Show ElfRewriteException
instance C.Exception ElfRewriteException

newtype ElfRewriter arch a = ElfRewriter { unElfRewrite :: S.StateT (RewriterInfo arch) IO a }
                          deriving (Monad,
                                    Functor,
                                    Applicative,
                                    IO.MonadIO,
                                    P.MonadThrow,
                                    S.MonadState (RewriterInfo arch))

emptyRewriterInfo :: E.Elf (MM.ArchAddrWidth arch) -> RewriterInfo arch
emptyRewriterInfo e = RewriterInfo { _riSegmentVirtualAddress    = Nothing
                                   , _riOverwrittenRegions       = []
                                   , _riAppendedSegments         = []
                                   , _riEntryPointAddress        = Nothing
                                   , _riSectionBaseAddress       = Nothing
                                   , _riInitialBytes             = Nothing
                                   , _riBlockRecoveryDiagnostics = []
                                   , _riRedirectionDiagnostics   = []
                                   , _riRecoveredBlocks          = Nothing
                                   , _riInstrumentationSites     = []
                                   , _riELF                      = e
                                   , _riSmallBlockCount          = 0
                                   , _riReusedByteCount          = 0
                                   , _riUnrelocatableTerm        = 0
                                   , _riOriginalTextSize         = 0
                                   , _riIncompleteBlocks         = 0
                                   , _riNewTextSize              = 0
                                   , _riBlockMapping             = []
                                   }
riOriginalTextSize :: L.Simple L.Lens (RewriterInfo arch) Int
riOriginalTextSize = GL.field @"_riOriginalTextSize"

riNewTextSize :: L.Simple L.Lens (RewriterInfo arch) Int
riNewTextSize = GL.field @"_riNewTextSize"

riIncompleteBlocks :: L.Simple L.Lens (RewriterInfo arch) Int
riIncompleteBlocks = GL.field @"_riIncompleteBlocks"

riSegmentVirtualAddress :: L.Simple L.Lens (RewriterInfo arch) (Maybe Word64)
riSegmentVirtualAddress = GL.field @"_riSegmentVirtualAddress"

riOverwrittenRegions :: L.Simple L.Lens (RewriterInfo arch) [(String, Word64)]
riOverwrittenRegions = GL.field @"_riOverwrittenRegions"

riAppendedSegments :: L.Simple L.Lens (RewriterInfo arch) [(E.ElfSegmentType, Word16, Word64, Word64)]
riAppendedSegments = GL.field @"_riAppendedSegments"

riEntryPointAddress :: L.Simple L.Lens (RewriterInfo arch) (Maybe Word64)
riEntryPointAddress = GL.field @"_riEntryPointAddress"

riSectionBaseAddress :: L.Simple L.Lens (RewriterInfo arch) (Maybe Word64)
riSectionBaseAddress = GL.field @"_riSectionBaseAddress"

riInitialBytes :: L.Simple L.Lens (RewriterInfo arch) (Maybe B.ByteString)
riInitialBytes = GL.field @"_riInitialBytes"

riBlockRecoveryDiagnostics :: L.Simple L.Lens (RewriterInfo arch) [RD.Diagnostic]
riBlockRecoveryDiagnostics = GL.field @"_riBlockRecoveryDiagnostics"

riRedirectionDiagnostics :: L.Simple L.Lens (RewriterInfo arch) [RD.Diagnostic]
riRedirectionDiagnostics = GL.field @"_riRedirectionDiagnostics"

riRecoveredBlocks :: L.Simple L.Lens (RewriterInfo arch) (Maybe SomeBlocks)
riRecoveredBlocks = GL.field @"_riRecoveredBlocks"

riInstrumentationSites :: L.Simple L.Lens (RewriterInfo arch) [RW.RewriteSite arch]
riInstrumentationSites = GL.field @"_riInstrumentationSites"

riSmallBlockCount :: L.Simple L.Lens (RewriterInfo arch) Int
riSmallBlockCount = GL.field @"_riSmallBlockCount"

riReusedByteCount :: L.Simple L.Lens (RewriterInfo arch) Int
riReusedByteCount = GL.field @"_riReusedByteCount"

riUnrelocatableTerm :: L.Simple L.Lens (RewriterInfo arch) Int
riUnrelocatableTerm = GL.field @"_riUnrelocatableTerm"

riBlockMapping :: L.Simple L.Lens (RewriterInfo arch) [(RA.ConcreteAddress arch, RA.ConcreteAddress arch)]
riBlockMapping = GL.field @"_riBlockMapping"
