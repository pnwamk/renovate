{-# LANGUAGE FlexibleContexts #-}
-- | This module is the entry point for binary code redirection
module Renovate.Redirect (
  redirect,
  LayoutStrategy(..),
  Diagnostic(..),
  ConcreteBlock,
  SymbolicBlock,
  BasicBlock(..),
  RelAddress(..),
  SymbolicAddress,
  TaggedInstruction
  ) where

import GHC.TypeLits ( KnownNat )

import Control.Arrow ( (***) )
import qualified Control.Monad.Catch as E
import Control.Monad.Trans ( lift )
import qualified Data.Foldable as F
import qualified Data.List as L
import Data.Ord ( comparing )
import qualified Data.Traversable as T
import Data.Typeable ( Typeable )

import Prelude

import qualified Data.Macaw.Memory as MM

import Renovate.Address
import Renovate.BasicBlock
import Renovate.ISA
import Renovate.Redirect.Concretize
import Renovate.Redirect.LayoutBlocks.Types ( LayoutStrategy(..)
                                            , Status(..)
                                            , LayoutPair(..) )
import Renovate.Redirect.Symbolize
import Renovate.Redirect.Internal
import Renovate.Redirect.Monad

-- | Given a list of basic blocks with instructions of type @i@ with
-- annotation @a@ (which is fixed by the 'ISA' choice), rewrite the
-- blocks to redirect execution to alternate blocks that have been
-- instrumented with the provided @instrumentor@.  The instrumentor is
-- applied to each redirected basic block.  The new blocks are laid
-- out starting at the new start address, which will typically be in a
-- different section.
--
-- The output blocks are returned in order by address.
--
-- The function runs in an arbitrary 'Monad' to allow instrumentors to
-- carry around their own state.
--
redirect :: (Monad m, InstructionConstraints i a, KnownNat w, MM.MemWidth w, Typeable w)
         => ISA i a w
         -- ^ Information about the ISA in use
         -> (SymbolicBlock i a w -> m (Maybe [TaggedInstruction i a]))
         -- ^ Instrumentor
         -> MM.Memory w
         -- ^ The memory space
         -> LayoutStrategy
         -> RelAddress w
         -- ^ The start address for the copied blocks
         -> [ConcreteBlock i w]
         -- ^ The original basic blocks
         -> SymbolMap w
         -> m (Either E.SomeException ([ConcreteBlock i w], [ConcreteBlock i w]), NewSymbolsMap w, [Diagnostic])
redirect isa instrumentor mem strat layoutAddr blocks symmap = runRewriterT isa symmap $ do
  baseSymBlocks <- symbolizeBasicBlocks mem (L.sortBy (comparing basicBlockAddress) blocks)
  transformedBlocks <- T.forM baseSymBlocks $ \(cb, sb) -> do
    insns' <- lift $ instrumentor sb
    case insns' of
      Nothing      -> return (LayoutPair cb sb Unmodified)
      Just insns'' -> return (LayoutPair cb sb { basicBlockInstructions = insns'' } Modified)
  concretizedBlocks <- concretize strat mem layoutAddr transformedBlocks
  redirectedBlocks <- redirectOriginalBlocks concretizedBlocks
  let sorter = L.sortBy (comparing basicBlockAddress)
  return $ (sorter *** sorter) (unzip (F.toList redirectedBlocks))

{- Note [Redirection]

The redirection is complex, but can be essentially broken down into
the following steps:

1) Create a symbolic index of all of the jumps in all of the basic
blocks.

2) Make a copy of each basic block; the copies will be placed in the
same order as the originals, but far away in the address space.  This
is necessary to let fallthroughs in conditional jumps continue to
work.  Note that we do not know the addresses of the new blocks at
this stage, since they might shift around as we apply the
instrumentation transformer.

3) Apply the instrumentor function to each copied basic block to
produce the fragile version.  After all of the blocks are transformed,
we can then lay them out and concretize their addresses.

4) Stitch control flow back together.  This involves fixing up all of
the relative symbolic jumps in the copied blocks to have their
concrete addresses (post instrumentation).

5) Rewrite the entry point of each of the original blocks that can
hold an absolute jump to the copied version.

6) Rewrite all of the absolute jumps in the program to point from old
blocks to new blocks.

Special handling for:

* Jump tables

Representation notes:

* We only need the addresses of basic blocks, as we can jump to those.
The addresses of individual instructions are not very important.  We
don't track them for individual instructions to avoid the headache of
ensuring their consistency with the basic block addresses.  We do need
the address of an individual instruction when resolving relative
jumps, though...

How can we express "this instruction really points to symbolic address
X"?  The problem is that we probably don't want to actually rewrite
instructions up front (in the instrumented blocks).  Instead, we
probably want to maintain an index on the side that will tell us how
to tweak the instructions later on.

Note that we aren't going to be aggressively rewriting jumps in the
uninstrumented code at all.

-}
