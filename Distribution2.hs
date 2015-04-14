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
import           Data.Set (Set, member)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.List (foldl')

-- | A probability distribution with probabilities of type @p@ and
-- outcomes/events of type @e@.
data Distribution p o = Distribution !(DTree p o) !(Set o) !Word deriving Show


data DTree p o = Leaf
               | DTree !o !p !p !Word !(DTree p o) !(DTree p o)
               deriving Show

outcomeOf (DTree o _ _ _ _ _) = o
probOf    Leaf                = 0
probOf    (DTree _ p _ _ _ _) = p
sumOf     Leaf                = 0
sumOf     (DTree _ _ s _ _ _) = s
countOf   Leaf                = 0
countOf   (DTree _ _ _ c _ _) = c
leftOf    (DTree _ _ _ _ l _) = l
rightOf   (DTree _ _ _ _ _ r) = r



insert :: (Ord o, Num p, Ord p) => (o,p) -> Distribution p o -> Distribution p o
insert (o',p') (Distribution tree outcomes dups) = if dups' * 2 <= countOf tree
    then Distribution tree' outcomes' dups' -- Not too many repeated elements
    else fromUniqList . toList $ Distribution tree' outcomes' 0
    where
    dups' = if o' `member` outcomes then dups + 1 else dups
    outcomes' = Set.insert o' outcomes
    tree' = insertTree (o',p') tree

empty :: (Num p) => Distribution p o
empty = Distribution Leaf Set.empty 0

reduce :: (Ord o, Num p) => [(o,p)] -> Map.Map o p
reduce = foldl' (\map (o,p) -> Map.insertWith (+) o p map) Map.empty
-- | @O(n*log(n))@ amortized. 
fromList :: (Ord o, Num p, Ord p) => [(o,p)] -> Distribution p o
fromList xs = fromUniqList . Map.toList . reduce $ xs
-- | @O(n*log(n))@.
toList :: (Ord o, Num p) => Distribution p o -> [(o,p)]
toList dist = Map.toList . reduce . toRepeatList $ dist

-- | Assumes there are no repeated items in the list. @O(n*log(n))@ amortized.
fromUniqList :: (Ord o, Num p, Ord p) => [(o,p)] -> Distribution p o
fromUniqList xs = foldl' (\dist pair -> insert pair dist) empty xs
-- | Doesn't bother to eliminate repeats. @O(n)@
toRepeatList :: Distribution p o -> [(o,p)]
toRepeatList = foldrWithP (:) []

-- | A right-associative fold on the tree structure, including the
-- probabilities. Note that outcomes may be repeated within the data structure.
foldrWithP :: ((o,p) -> b -> b) -> b -> Distribution p o -> b
foldrWithP f b (Distribution tree _ _) = foldrTreeWithP f b tree

foldrTreeWithP :: ((o,p) -> b -> b) -> b -> DTree p o -> b
foldrTreeWithP f b Leaf = b
foldrTreeWithP f b (DTree o p _ _ l r) = foldrTreeWithP f (f (o,p) (foldrTreeWithP f b r)) l

-- | @O(log(n))@ amortized.
-- Will not overwrite existing @(o,p)@ pairs in the distribution.
-- Inserting @(o,p1)@ and @(o,p2)@ is equivalent to inserting @(o,p1+p2)@.
insertTree :: (Ord o, Num p, Ord p) => (o,p) -> DTree p o -> DTree p o
insertTree (o',p') Leaf = DTree o' p' p' 1 Leaf Leaf
insertTree (o',p') (DTree o p s c l r)
    | p' <= p = if countOf l < countOf r
        then DTree o  p  s' c' (insertTree (o',p') l) r
        else DTree o  p  s' c' l                      (insertTree (o',p') r)
    | p' >  p = if countOf l < countOf r
        then DTree o' p' s' c' (insertTree (o,p)   l) r
        else DTree o' p' s' c' l                      (insertTree (o,p)   r)
    where
    s' = s + p'
    c' = c + 1

sizeInvariant :: (Num p, Eq p) => DTree p e -> Bool
sizeInvariant Leaf = True
sizeInvariant (DTree e p s c l r) = (c == countOf l + countOf r + 1) &&
                                       (countOf l <= countOf r + 1) &&
                                       (countOf r <= countOf l + 1) &&
                                       sizeInvariant l &&
                                       sizeInvariant r

sumInvariant :: (Num p, Eq p) => DTree p e -> Bool
sumInvariant Leaf = True
sumInvariant (DTree e p s c l r) = (s == p + sumOf l + sumOf r) && 
                                 (sumInvariant l) &&
                                 (sumInvariant r)

heapInvariant :: (Ord p, Num p) => DTree p e -> Bool
heapInvariant Leaf = True
heapInvariant (DTree e p s c l r) = (p > probOf l) &&
                                  (p > probOf r) &&
                                  heapInvariant l &&
                                  heapInvariant r

zeroInvariant :: (Ord p, Num p) => DTree p e -> Bool
zeroInvariant Leaf = True
zeroInvariant (DTree _ p _ c l r) = (p /= 0) && 
                                  zeroInvariant l && 
                                  zeroInvariant r

invariants :: (Num p, Ord p, Ord e) => Distribution p e -> Bool
invariants (Distribution tree members dups)
    | not (sumInvariant  tree) = error "Sum invariant failure"
    | not (heapInvariant tree) = error "Heap invariant failure"
    | not (zeroInvariant tree) = error "Zero-chance values present"
    | not (sizeInvariant tree) = error "Tree is not balanced correctly"
    | otherwise                = True


