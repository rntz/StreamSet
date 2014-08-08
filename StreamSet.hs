{-# LANGUAGE ScopedTypeVariables #-}

-- A (potentially infinite) set, which can be lazily converted to a list without
-- forcing all of its keys at once (unlike Data.Set, which cannot be infinite
-- and forces all of its keys).
--
-- TODO: runtime analysis
--
-- It may help to think of this as "a stream without duplicates", except that
-- operations aren't required to preserve order (enumerability, however, must be
-- preserved).
module StreamSet
    ( StreamSet
    , null, member
    , empty, singleton, insert
    , fromList, fromUniqueList, fromFiniteList, fromFiniteSet, toList
    , union, unions, filter, map, unionMap
    , mapInjective, unionDisjoint, unionsDisjoint, unionMapDisjoint
    , cartesianProduct, map2
    -- , fix, isSubsetOf
    , finiteFix
    )
where

import Prelude hiding (filter, map, nub, null)

import Data.Set (Set)
import Data.Maybe (mapMaybe)
import qualified Data.List as List
import qualified Data.Set as Set

data StreamSet a = Lists { raw :: [a]    -- finite # of duplicates allowed
                         , toList :: [a] -- no duplicates allowed
                         }

instance Show a => Show (StreamSet a) where
    -- only shows first 10 elements, with a "..." if there are more
    show x = "{"
             ++ List.intercalate ", " (take 10 l)
             ++ (if length (take 11 l) < 11 then "" else "...")
             ++ "}"
        where l = List.map show $ toList x


-- Utility
nub :: Ord a => [a] -> [a]
nub l = dedup Set.empty l

dedup :: Ord a => Set a -> [a] -> [a]
dedup s (x:xs)
    | Set.member x s = dedup s xs
dedup s (x:xs) = x : dedup newS xs
    where newS = Set.insert x s
dedup _ [] = []

finiteNub :: Ord a => [a] -> [a]
finiteNub = Set.toList . Set.fromList

getHead :: [a] -> Maybe (a,[a])
getHead (a:as) = Just (a,as)
getHead [] = Nothing

-- lazy in its second argument, at least until it destructs its first
interleave :: [a] -> [a] -> [a]
interleave (a:as) bs = a : interleave bs as
interleave [] bs = bs

-- does the classic "triangular" enumeration of (N x N) where N is the naturals,
-- generalized to a (possibly) infinite list of (possibly) infinite lists.
--
-- for reference, the "triangular" enumeration of N x N is:
--     [(0,0),
--      (1,0), (0,1),
--      (2,0), (1,1), (0,2),
--      (3,0), (2,1), (1,2), (0,3),
--      ...]
--
-- TODO?: generalize to n dimensions?
cross :: [a] -> [b] -> [(a,b)]
cross xs ys = interleaves [[(x,y) | y <- ys] | x <- xs]

interleaves :: [[a]] -> [a]
interleaves [] = []
interleaves (l:ls) = taker [l] ls
    where taker l ls =
              let (as, l') = unzip $ mapMaybe getHead l
              in as ++ case ls of [] -> taker l' []
                                  (l:ls) -> taker (l:l') ls


-- Queries
null :: StreamSet a -> Bool
null (Lists [] []) = True
null _ = False

-- WARNING: partial function! if s is infinite and x is not an element, this
-- never returns.
member :: Ord a => a -> StreamSet a -> Bool
member x s = elem x (toList s)


-- Constructors
empty :: StreamSet a
empty = Lists [] []

singleton :: Ord a => a -> StreamSet a
singleton x = Lists [x] [x]

-- avoid using insert unless absolutely necessary. really bad perf.
insert :: Ord a => a -> StreamSet a -> StreamSet a
insert x (Lists raw elems) = Lists (x:raw) (x : List.filter (/= x) elems)

fromList :: Ord a => [a] -> StreamSet a
fromList l = Lists l (nub l)

fromUniqueList :: Ord a => [a] -> StreamSet a
fromUniqueList l = Lists l l

fromFiniteSet :: Ord a => Set a -> StreamSet a
fromFiniteSet s = fromUniqueList (Set.toList s)

fromFiniteList :: Ord a => [a] -> StreamSet a
fromFiniteList = fromFiniteSet . Set.fromList

-- pulls an element off of its left argument before it forces its right to WHNF.
-- this property is important for constructing e.g. infinite unions.
union :: Ord a => StreamSet a -> StreamSet a -> StreamSet a
union a b | null a = b
-- we use raw to avoid having lots of intermediate nubbing Sets lying around
union a b = fromList $ interleave (raw a) (raw b)

-- the sets you provide must be disjoint!
-- like union, lazy in its second argument.
unionDisjoint :: Ord a => StreamSet a -> StreamSet a -> StreamSet a
unionDisjoint a b | null a = b
-- note that we carefully avoid destructing b
unionDisjoint (Lists araw alist) b
    = Lists (interleave araw (raw b)) (interleave alist (toList b))

unions :: Ord a => [StreamSet a] -> StreamSet a
unions [] = empty
-- TODO: think about whether this can produce a list with infinitely many
-- duplicates in its `raw`
--
-- we use raw to avoid having lots of intermediate nubbing Sets lying around
unions sets = fromList $ interleaves [raw s | s <- sets]

-- the sets you provide must be disjoint!
-- TODO: consider order of enumeration
unionsDisjoint :: Ord a => [StreamSet a] -> StreamSet a
unionsDisjoint [] = empty
unionsDisjoint xs = foldr1 unionDisjoint xs

filter :: Ord a => (a -> Bool) -> StreamSet a -> StreamSet a
filter p (Lists raw nodups) = Lists (List.filter p raw) (List.filter p nodups)

map :: (Ord b) => (a -> b) -> StreamSet a -> StreamSet b
map f s = fromList $ List.map f $ raw s

-- the function you provide must be injective!
mapInjective :: Ord b => (a -> b) -> StreamSet a -> StreamSet b
mapInjective f (Lists raw nodups) = Lists (List.map f raw) (List.map f nodups)

unionMap :: (Ord b) => (a -> StreamSet b) -> StreamSet a -> StreamSet b
unionMap f s = unions $ List.map f $ toList s

-- the function you give must map distinct values to disjoint sets!
unionMapDisjoint :: Ord b => (a -> StreamSet b) -> StreamSet a -> StreamSet b
unionMapDisjoint f s = unionsDisjoint $ List.map f $ toList s


-- Some set operations
-- TODO: think about enumeration order!
cartesianProduct :: (Ord a, Ord b) =>
                    StreamSet a -> StreamSet b -> StreamSet (a,b)
cartesianProduct as bs = Lists (cross (raw as) (raw bs))
                               (cross (toList as) (toList bs))

map2 :: (Ord a, Ord b, Ord c) =>
        (a -> b -> c) -> StreamSet a -> StreamSet b -> StreamSet c
map2 f as bs = map (uncurry f) (cartesianProduct as bs)


-- the function had better be monotonic!
-- ONLY WORKS ON FINITE SETS
fix :: Ord a => (StreamSet a -> StreamSet a) -> StreamSet a
fix f = fixFrom f empty

fixFrom :: Ord a => (StreamSet a -> StreamSet a) -> StreamSet a -> StreamSet a
fixFrom func init =
    -- let's assume that all sets are finite, for now.
    let next = func init
    in if isSubsetOf next init
       then init
       else init `union` fixFrom func next

-- ONLY WORKS FOR FINITE SETS
isSubsetOf :: Ord a => StreamSet a -> StreamSet a -> Bool
isSubsetOf a b = all (`member` b) (toList a)

-- in order to deal with infinite sets, what we need to do is:
-- take the union of init with the fix point from next.
-- BUT as soon as it becomes clear next is finite, check whether
-- it's a subset of init, and if so, halt.

-- A limited fixed-point. A finite seed + a finite "expand" function; can
-- nonetheless give rise to infinite sets (consider expand x = Set.fromList
-- [x*2], which gives rise to all powers of two of elements of the seed set).
--
-- For more fun, consider:
--
--     weird = finiteFix (Set.singleton . collatz)
--     collatz n | even n = n `div` 2
--               | otherwise = 3 * n + 1
--
-- This computes all numbers touched by the collatz sequences of numbers in the
-- given initial set; and it avoids recomputation of the trailing sequences of
-- any numbers already visited (i.e. it "memoizes").
finiteFix :: forall a. Ord a => (a -> Set a) -> Set a -> StreamSet a
finiteFix expand init = iter init init
    where
      -- in iter, frontier is a subset of sofar
      iter :: Ord a => Set a -> Set a -> StreamSet a
      iter sofar frontier | Set.null frontier = empty
      iter sofar frontier =
          fromFiniteSet frontier `union`
          grow sofar (Set.unions $ List.map expand $ Set.toList frontier)
      -- in grow, expandedFrontier may include elements in sofar
      grow :: Ord a => Set a -> Set a -> StreamSet a
      grow sofar expandedFrontier =
          let frontier = (Set.difference expandedFrontier sofar)
          in iter (Set.union sofar frontier) frontier
