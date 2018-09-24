{-# LANGUAGE FlexibleContexts #-}
-- | Define the strategy for laying out 'SymbolicBlock's
module Renovate.Redirect.LayoutBlocks (
  layoutBlocks,
  LayoutStrategy(..),
  LoopStrategy(..),
  loopStrategy,
  CompactOrdering(..)
  ) where

import           Control.Monad.IO.Class
import           Data.Map (Map)
import qualified Data.Traversable as T

import           Renovate.Address
import           Renovate.BasicBlock ( InstructionConstraints )
import           Renovate.Recovery ( SymbolicCFG )
import           Renovate.Redirect.Monad
import           Renovate.Redirect.LayoutBlocks.Compact ( compactLayout )
import           Renovate.Redirect.LayoutBlocks.Types ( LayoutStrategy(..)
                                                      , LoopStrategy(..)
                                                      , loopStrategy
                                                      , CompactOrdering(..)
                                                      , SymbolicPair
                                                      , AddressAssignedPair )

-- | Compute a concrete address for each 'SymbolicBlock'.
--
-- Right now, we use an inefficient encoding of jumps.  We could do
-- better later on.
layoutBlocks :: (MonadIO m, T.Traversable t, InstructionConstraints arch)
             => LayoutStrategy
             -> ConcreteAddress arch
             -- ^ Address to begin block layout of instrumented blocks
             -> t (SymbolicPair arch)
             -> Map (ConcreteAddress arch) (SymbolicCFG arch)
             -> RewriterT arch m [AddressAssignedPair arch]
layoutBlocks strat startAddr blocks cfgs =
  compactLayout startAddr strat blocks cfgs
