{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Numeric.Probability.Distribution
-- Copyright   :  (c) William Yager 2015
-- License     :  MIT
-- Maintainer  :  will (dot) yager (at) gmail (dot) com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module provides a data structure and associated functions for
-- representing discrete probability distributions.
-- 
-- The data structure is optimized for fast sampling from the distribution.
--
-- Complexity of the various operations on the data structure is
-- complicated, as the structure enforces a BST property on the events/outcomes
-- but enforces a heap structure on the probabilities. Therefore, more likely
-- outcomes will be sampled faster than unlikely outcomes, which is great for
-- sampling lots of random events, but may lead to O(n) performance in 
-- certain pathological cases.
-----------------------------------------------------------------------------

module Numeric.Probability.Distribution (

) where

import Prelude hiding (product, sum, zipWith)
import Control.Monad.Random (MonadRandom, Random, getRandomRs)
import Data.Monoid (Monoid, mempty, mappend)
import Data.Word (Word)
import           Data.Set.Strict (Set, member)
import qualified Data.Set.Strict as Set
import qualified Data.Map.Strict as Map

-- | A probability distribution with probabilities of type @p@ and
-- outcomes/events of type @e@.
data Distribution p o = Distribution !(DTree p o) !(Set o) !Word


data DTree p o = Leaf
               | DTree !o !p !p !Word !(Distribution p o) !(Distribution p o)

outcomeOf (DTree o _ _ _ _ _) = o
probOf    Leaf                = 0
probOf    (DTree _ p _ _ _ _) = p
sumOf     Leaf                = 0
sumOf     (DTree _ _ s _ _ _) = s
countOf   Leaf                = 0
countOf   (DTree _ _ _ c _ _) = c
leftOf    (DTree _ _ _ _ l _) = l
leftOf    (DTree _ _ _ _ _ r) = r



insert :: (o,p) -> Distribution p o -> Distribution p o
insert (o',p') (Distribution tree outcomes dups) = if dups' * 2 < countOf tree
    then Distribution tree' outcomes' dups' -- Not too many repeated elements
    else fromUniqList . toList $ Distribution tree' empty 0 -- Too many repeats
    where
    dups' = if o' `member` outcomes then dups + 1 else dups
    outcomes' = Set.insert o' outcomes
    tree' = insertTree (o',p') tree

reduce = foldl' (\map (o,p) -> Map.insertWith (+) o p map) Map.empty
-- | @O(n*log(n))@ amortized. 
fromList :: [(o,p)] -> Distribution p o
fromList xs = fromUniqList . Map.toList . reduce $ xs
-- | @O(n*log(n))@.
toList :: Distribution p o -> [(o,p)]
toList dist = Map.toList . reduce . toRepeatList $ dist

-- | Assumes there are no repeated items in the list. @O(n*log(n))@ amortized.
fromUniqList :: [(o,p)] -> Distribution p o
fromUniqList xs = Distribution tree Set.empty 0
    where
    tree = foldl' (\tree pair -> insertTree pair tree) Leaf xs
-- | Doesn't bother to eliminate repeats. @O(n)@
toRepeatList :: Distribution p o -> [(o,p)]

-- | @O(log(n))@ amortized.
-- Will not overwrite existing @(o,p)@ pairs in the distribution.
-- Inserting @(o,p1)@ and @(o,p2)@ is equivalent to inserting @(o,p1+p2)@.
insertTree :: (o,p) -> DTree p o -> DTree p o
insertTree (o',p') Leaf = DTree o' p' p' 1 Leaf Leaf
insertTree (o',p') (DTree o p s c l r)
    | p' <= p = if countOf l < countOf r
        then DTree o  p  s' c' (insertTree (o',p') l) r
        else DTree o  p  s' c' l                      (insertTree (o',p') r)
    | p' >  p = if countOf l < countOf r
        then DTree o' p' s' c' (insertTree (o,p) l)   r
        else DTree o' p' s' c' l                      (insertTree (o,p) r)
    where
    s' = s + p
    c' = c + 1