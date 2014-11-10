{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Security.InfoFlow.Policy.FlowLocks.Lattice
-- Copyright   :  (c) Niklas Broberg 2013
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Niklas Broberg, niklas.broberg@chalmers.se
-- Stability   :  transient
-- Portability :  portable
--
-- This module provides a common interface to lattices,
-- allowing monadic the operations to be monadic
-- (typically to access an environment).
--
-----------------------------------------------------------------------------
module Security.InfoFlow.Policy.FlowLocks.Lattice
    (
     -- * Lattice class
     PartialOrder(..), JoinSemiLattice(..), Lattice(..),

     -- * Further operations
     geq, mayBeTop, mustBeTop, mayBeBottom, mustBeBottom,

     topM, bottomM,

     -- * Convenient helpers
     forall, exists

    ) where

import Control.Monad (liftM)
import Control.Applicative

class (Eq point, Functor m, Applicative m, Monad m) =>
    PartialOrder m point | point -> m where
  -- | Partial order operation
    leq :: point -> point -> m Bool


-- | Class representing a join semi-lattice. We separate
--   join semi-lattices from full lattices since we only
--   require join and top from distinguished actor sets.
--   We parameterise over a monad to allow join to e.g.
--   query an environment.
--   Minimal instantiation requires 'lub' and 'top'.
class PartialOrder m point =>
    JoinSemiLattice m point where
    -- | Least upper bound operation
    lub :: point -> point -> m point
    -- | Top element must exist
    top  :: point

    -- | Check if a given point is equivalent to 'top'.
    --   We allow it to be overridden for efficiency
    --   purposes.
    --   We use a three-valued logic to account, making
    --   it possible to distinguish the cases of when
    --   something *may* be top, and when something *is*
    --   top for certain.
    isTop :: point -> m (Maybe Bool)
    isTop p = return $ Just (p == top)
    
      
-- | Reversed partial order operation
geq :: PartialOrder m point => 
       point -> point -> m Bool
geq = flip leq

-- | A monadic version of 'top', useful
--   in places where the @m@ parameter is ambiguous.
topM :: JoinSemiLattice m point => m point
topM = return top


-- | Class representing a full lattice, to be used for
--   Policies in general. Minimal instantiation is
--   'meet' and 'bottom'.

class JoinSemiLattice m point => 
    Lattice m point where
    -- | Greatest lower bound operation
    glb :: point -> point -> m point
    -- | Bottom element must exist
    bottom :: point

    -- | Check if a given point is equivalent to 'bottom'.
    --   Can be overridden to provide more efficient 
    --   implementation.
    --   We use a three-valued logic just as for 'isTop'.
    isBottom :: point -> m (Maybe Bool)
    isBottom p = return $ Just (p == bottom)


-- | A monadic version of 'top', useful
--   in places where the @m@ parameter is ambiguous.
bottomM :: Lattice m point => m point
bottomM = return bottom

-- | Returns true if it is possible that the
--   given value could be equivalent top 'top'
--   in the given (join semi-)lattice.
mayBeTop :: JoinSemiLattice m point =>
            point -> m Bool
mayBeTop point = do
  mb <- isTop point
  return $ maybe True id mb

-- | Returns true if it is guaranteed that the
--   given value is equivalent top 'top'
--   in the given (join semi-)lattice.
mustBeTop :: JoinSemiLattice m point =>
             point -> m Bool
mustBeTop point = do
  mb <- isTop point
  return $ maybe False id mb

-- | Returns true if it is possible that the
--   given value could be equivalent top 'top'
--   in the given (join semi-)lattice.
mayBeBottom :: Lattice m point =>
               point -> m Bool
mayBeBottom point = do
  mb <- isBottom point
  return $ maybe True id mb

-- | Returns true if it is possible that the
--   given value could be equivalent top 'top'
--   in the given (join semi-)lattice.
mustBeBottom :: Lattice m point =>
                point -> m Bool
mustBeBottom point = do
  mb <- isBottom point
  return $ maybe False id mb


-- | Typical use:
--   \forall x \in xs. 
--     \exists y \in ys.
--       x `leq` y
--   could be written as
-- @ 
--    forall xs $ \x -> 
--      exists ys $ \y -> 
--        x `leq` y
-- @
--
forall :: Monad m => [a] -> (a -> m Bool) -> m Bool
forall xs mTest = liftM and $ mapM mTest xs

exists :: Monad m => [a] -> (a -> m Bool) -> m Bool
exists xs mTest = liftM or $ mapM mTest xs