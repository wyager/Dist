{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving #-}

module Numeric.Probability.Distribution (
    Distribution,
    sumOf,
    insert,
    empty,
    toList,
    fromList,
    joint,
    sum,
    product,
    zipWith,
    foldrP,
    probabilityOf,
    sample,
    normalize
) where

import Prelude hiding (product, sum, zipWith)
import Control.Monad.Random (MonadRandom, Random, getRandomRs)
import Data.Monoid (Monoid, mempty, mappend)

-- | A probability distribution with probabilities of type @p@ and
-- outcomes/events of type @e@.
data Distribution p e = Leaf
                      | DTree {eventOf :: !e, probability :: !p, treeSum :: !p,
                               leftOf ::  !(Distribution p e),
                               rightOf :: !(Distribution p e)}
                      deriving (Eq)

instance (Ord e, Num p, Ord p) => Monoid (Distribution p e) where
    mempty = empty
    mappend = product

instance (Show p, Show e) => Show (Distribution p e) where
    show dist = "fromList " ++ show (toList dist)

-- | An empty distribution. Trying to sample from it will yield an error.
empty :: Distribution p e
empty = Leaf

-- | Re-weights the distribution so the sum of all probabilities is 1.
normalize :: Fractional p => Distribution p e -> Distribution p e
normalize dist = normalize' (sumOf dist) dist

normalize' :: Fractional p => p -> Distribution p e -> Distribution p e
normalize' d Leaf              = Leaf
normalize' d (DTree e p s l r) = DTree e (p/d) (s/d) (normalize' d l) (normalize' d r)

joinAscList :: (Ord e, Num p) => (e -> p -> p -> p) -> [(p,e)] -> [(p,e)] -> [(p,e)]
joinAscList f []           []         = []
joinAscList f ((p,e):xs)   []         = (f e p 0, e) : joinAscList f xs []
joinAscList f []           ((p,e):xs) = (f e 0 p, e) : joinAscList f [] xs
joinAscList f ((pa,ea):as) ((pb,eb):bs) 
    | ea == eb = (f ea pa pb, ea) : joinAscList f as           bs
    | ea >  eb = (f eb 0  pb, eb) : joinAscList f ((pa,ea):as) bs
    | ea <  eb = (f ea pa 0 , ea) : joinAscList f as           ((pb,eb):bs) 

-- | Combines two distributions using some function.
-- The function should take the value and the probability of the value in 
-- each distribution, and return a new probability. If a value is not present
-- in a distribution, it has probability zero. 
zipWithKey :: (Ord e, Ord p, Num p) => (e -> p -> p -> p) -> Distribution p e -> Distribution p e -> Distribution p e
zipWithKey f a b = fromList $ joinAscList f (toList a) (toList b)

-- | Combines two distributions using some function.
-- The function should take the probability of the value in each distribution 
-- and return a new probability. If a value is not present in a distribution,
-- it has probability zero. 
zipWith :: (Ord e, Ord p, Num p) => (p -> p -> p) -> Distribution p e -> Distribution p e -> Distribution p e
zipWith f a b = zipWithKey (\_ -> f) a b

-- | Adds the elements in each distribution. Equivalent to @'zipWith' (+)@.
sum :: (Ord e, Num p, Ord p) => Distribution p e -> Distribution p e -> Distribution p e
sum a b = foldrP (\(p,e) dist -> insert p e dist) a b

-- | Multiplies the distributions together. Equivalent to @'zipWith' (*)@.
product :: (Ord e, Num p, Ord p) => Distribution p e -> Distribution p e -> Distribution p e
product = zipWith (*) 

-- | Creates the joint distribution from two distributions.
joint :: (Num p, Ord p, Ord e1, Ord e2) => Distribution p e1 -> Distribution p e2 -> Distribution p (e1, e2)
joint d1 d2 = fromList [(p1*p2, (e1, e2)) | (p1, e1) <- toList d1, (p2, e2) <- toList d2]

-- | Converts the distribution to a list of (probability, outcome) pairs.
toList :: Distribution p e -> [(p,e)]
toList = foldrP (:) []

-- | A right-associative fold on the distribution.
foldrP :: ((p,e) -> b -> b) -> b -> Distribution p e -> b
foldrP _ b Leaf = b
foldrP f b (DTree e p _ l r) = foldrP f (f (p,e) (foldrP f b r)) l

-- | The probability of a given outcome
probabilityOf :: (Ord e, Num p) => Distribution p e -> e -> p
probabilityOf Leaf              _            = 0
probabilityOf (DTree e p _ l r) e' | e' == e = p
                                   | e' <  e = probabilityOf l e'
                                   | e' >  e = probabilityOf r e'

-- | Converts from a list of (probability, outcome) pairs to a distribution.
fromList :: (Ord e, Ord p, Num p) => [(p,e)] -> Distribution p e
fromList = foldl (\dist (p,e) -> insert p e dist) empty

nodeProbability :: Num p => Distribution p e -> p
nodeProbability Leaf = 0
nodeProbability (DTree _ p _ _ _) = p

-- | The total probability of the distribution. 
-- After normalization, this will be equal to 1.
sumOf :: Num p => Distribution p e -> p
sumOf Leaf = 0
sumOf (DTree _ _ s _ _) = s

-- invariants:
--     da leftOf db iff da < db
--     da rightOf db iff da > db
--     for all trees, the most likely thing in the tree is at the top
--     sum of a tree == the sum of all probabilities in that tree
--     No values with zero probability in the tree

-- | Inserts a (probability, outcome) pair into the distribution.
-- If the outcome is already in the distribution, the new probability will be 
-- added.
insert :: (Num p, Ord p, Ord e) => p -> e -> Distribution p e -> Distribution p e
insert 0     _      dist = dist
insert prob' event' Leaf = DTree event' prob' prob' Leaf Leaf
insert prob' event' (DTree event prob sum left right)
    | event' == event =           DTree event (prob + prob') sum' left  right
    | event' <  event = rotated $ DTree event prob           sum' left' right
    | event' >  event = rotated $ DTree event prob           sum' left  right'
    where
    left' @(DTree el pl sl ll rl) = insert prob' event' left
    right'@(DTree er pr sr lr rr) = insert prob' event' right
    rotated dist@(DTree e p s l r)
        | nodeProbability r > p = DTree er pr s (DTree e p (p + sumOf l + sumOf (leftOf r)) l (leftOf r)) (rightOf r)
        | nodeProbability l > p = DTree el pl s (leftOf l) (DTree e p (p + sumOf r + sumOf (rightOf l)) (rightOf l) r)
        | otherwise             = DTree e p s l r -- No need to do anything
    sum' = sum + prob'

-- Returns random value in range (0,n]
randomPositiveUpto :: (Eq n, Num n, Random n, MonadRandom m) => n -> m n
randomPositiveUpto n = do
    randoms <- getRandomRs (0,n)
    return . head . dropWhile (==0) $ randoms

-- | Take a sample from the distribution. Can be used with e.g. @evalRand@
-- or @evalRandIO@ from @Control.Monad.Random@.
sample :: (Ord p, Num p, Random p, MonadRandom m) => Distribution p e -> m e
sample Leaf = error "Error: Can't sample an empty distribution"
sample (DTree event prob sum l r) = do
    index <- randomPositiveUpto sum
    let result | index > sumOf l + prob = sample r
               | index > sumOf l        = return event
               | index > 0              = sample l
    result

sumInvariant :: (Num p, Eq p) => Distribution p e -> Bool
sumInvariant Leaf = True
sumInvariant (DTree e p s l r) = (s == p + sumOf l + sumOf r) && 
                                 (sumInvariant l) &&
                                 (sumInvariant r)

bstInvariant :: (Ord e, Eq p) => Distribution p e -> Bool
bstInvariant Leaf = True
bstInvariant (DTree e p s l r) = (l == Leaf || eventOf l < e) &&
                                 (r == Leaf || eventOf r > e) &&
                                 bstInvariant l &&
                                 bstInvariant r

heapInvariant :: (Ord p, Num p) => Distribution p e -> Bool
heapInvariant Leaf = True
heapInvariant (DTree e p s l r) = (p > nodeProbability l) &&
                                  (p > nodeProbability r) &&
                                  heapInvariant l &&
                                  heapInvariant r

zeroInvariant :: (Ord p, Num p) => Distribution p e -> Bool
zeroInvariant Leaf = True
zeroInvariant (DTree _ p _ l r) = (p /= 0) && 
                                  zeroInvariant l && 
                                  zeroInvariant r

invariants :: (Num p, Ord p, Ord e) => Distribution p e -> Bool
invariants dist | not (sumInvariant  dist) = error "Sum invariant failure"
                | not (bstInvariant  dist) = error "BST invariant failure"
                | not (heapInvariant dist) = error "Heap invariant failure"
                | not (zeroInvariant dist) = error "Zero-chance values present"
                | otherwise                = True

test = foldl (flip $ uncurry insert) Leaf [(1,"a"),(2,"b"),(1,"c"),(7,"d"),(9,"e"),(7,"f")]
testF = foldl (flip $ uncurry insert) Leaf [(1.0,"a"),(2.0,"b"),(1.0,"c"),(7.0,"d"),(9.0,"e"),(7.0,"f")]