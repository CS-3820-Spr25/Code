{-# LANGUAGE FlexibleInstances, InstanceSigs, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <&>" "Use <$>" #-}
module Lecture10 where

import Control.Applicative
import Control.Monad (guard, liftM2)

import Data.Function (on)
import Data.List (groupBy, sortBy)

import Prelude hiding (Maybe(..), Either(..))

data Maybe a = Nothing | Just a

--------------------------------------------------------------------------------

instance Functor Maybe where
  fmap :: (a -> b) -> Maybe a -> Maybe b
  fmap f (Just x) = Just (f x)
  fmap f Nothing = Nothing

instance Applicative Maybe where
  pure :: a -> Maybe a
  pure = Just

  (<*>) :: Maybe (a -> b) -> Maybe a -> Maybe b
  Just f <*> Just x = Just (f x)
  _ <*> _ = Nothing

instance Monad Maybe where
  return :: a -> Maybe a 
  return = Just

  (>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
  Nothing >>= _ = Nothing
  Just x >>= k  = k x

---------------------------------------------------------------------------------

data Either a b = Left a | Right b

instance Monad (Either a) where
  return :: b -> Either a b
  return = Right

  (>>=) :: Either a b -> (b -> Either a c) -> Either a c
  Left x >>= _ = Left x
  Right x >>= k = k x

instance Functor (Either a) where
  fmap :: (b -> c) -> Either a b -> Either a c
  fmap f m = m >>= return . f 

instance Applicative (Either a) where
  pure :: b -> Either a b
  pure = return

  (<*>) :: Either a (b -> c) -> Either a b -> Either a c
  ef <*> ex = do f <- ef
                 x <- ex
                 return (f x)

--------------------------------------------------------------------------------
                 
class Monad m => MonadExcept e m where
  throw :: e -> m a
  catch :: m a -> (e -> m a) -> m a

instance MonadExcept () Maybe where
  throw :: () -> Maybe a
  throw () = Nothing
  
  catch :: Maybe a -> (() -> Maybe a) -> Maybe a
  catch Nothing h = h ()
  catch (Just x) _ = Just x

instance MonadExcept a (Either a) where
  throw :: a -> Either a b   
  throw x = Left x
  catch :: Either a b -> (a -> Either a b) -> Either a b
  catch (Left x) h = h x
  catch (Right x) _ = Right x
  
--------------------------------------------------------------------------------

type Probability = Float -- But use ratio int for the beginning
newtype Dist a = Dist [(a, Probability)]

raw :: Dist a -> [(a, Probability)]
raw (Dist d) = d

instance Functor Dist where
    fmap :: (a -> b) -> Dist a -> Dist b
    fmap f (Dist d) = Dist [(f a, p) | (a, p) <- d]

instance Applicative Dist where
    pure :: a -> Dist a
    pure = return

    (<*>) :: Dist (a -> b) -> Dist a -> Dist b
    (<*>) = liftM2 ($)

instance Monad Dist where
    return :: a -> Dist a
    return a = Dist [(a, 1)]

    (>>=) :: Dist a -> (a -> Dist b) -> Dist b
    Dist d >>= k = Dist (concatMap kf d) where
        kf (a, p) = [(b, p * q) | (b, q) <- d'] where
            Dist d' = k a

-- Coin flip:

instance Alternative Dist where
    empty :: Dist a
    empty = Dist []

    (<|>) :: Dist a -> Dist a -> Dist a
    Dist d <|> Dist e = Dist ([(a, 0.5 * p) | (a, p) <- d] ++ [(a, 0.5 * p) | (a, p) <- e])

-- >>> raw (return True <|> return False)
-- [(True,0.5),(False,0.5)]

-- >>> raw (return 1 <|> return 2 <|> return 3)
-- [(1,0.25),(2,0.25),(3,0.5)]

-- Dice:

uniform :: [a] -> Dist a
uniform as = Dist [(a, 1 / n) | a <- as]
    where n = fromIntegral (length as)

-- >>> raw (uniform [1..6])
-- [(1,0.16666667),(2,0.16666667),(3,0.16666667),(4,0.16666667),(5,0.16666667),(6,0.16666667)]

dice :: Int -> Dist [Int]
dice 0 = return []
dice n = do d <- uniform [1..6]
            ds <- dice (n - 1)
            return (d : ds)

-- >>> raw (dice 2)
-- [([1,1],1 % 36),([1,2],1 % 36),([1,3],1 % 36),([1,4],1 % 36),([1,5],1 % 36),([1,6],1 % 36),([2,1],1 % 36),([2,2],1 % 36),([2,3],1 % 36),([2,4],1 % 36),([2,5],1 % 36),([2,6],1 % 36),([3,1],1 % 36),([3,2],1 % 36),([3,3],1 % 36),([3,4],1 % 36),([3,5],1 % 36),([3,6],1 % 36),([4,1],1 % 36),([4,2],1 % 36),([4,3],1 % 36),([4,4],1 % 36),([4,5],1 % 36),([4,6],1 % 36),([5,1],1 % 36),([5,2],1 % 36),([5,3],1 % 36),([5,4],1 % 36),([5,5],1 % 36),([5,6],1 % 36),([6,1],1 % 36),([6,2],1 % 36),([6,3],1 % 36),([6,4],1 % 36),([6,5],1 % 36),([6,6],1 % 36)]

-- >>> raw (sum <$> dice 2)
-- [(2,1 % 36),(3,1 % 36),(4,1 % 36),(5,1 % 36),(6,1 % 36),(7,1 % 36),(3,1 % 36),(4,1 % 36),(5,1 % 36),(6,1 % 36),(7,1 % 36),(8,1 % 36),(4,1 % 36),(5,1 % 36),(6,1 % 36),(7,1 % 36),(8,1 % 36),(9,1 % 36),(5,1 % 36),(6,1 % 36),(7,1 % 36),(8,1 % 36),(9,1 % 36),(10,1 % 36),(6,1 % 36),(7,1 % 36),(8,1 % 36),(9,1 % 36),(10,1 % 36),(11,1 % 36),(7,1 % 36),(8,1 % 36),(9,1 % 36),(10,1 % 36),(11,1 % 36),(12,1 % 36)]

norm :: Ord a => Dist a -> [(a, Probability)]
norm (Dist d) = [(a, sum ps / q) | d' <- ds, let (a : _, ps) = unzip d']
    where q = sum (map snd d)
          ds = groupBy ((==) `on` fst) (sortBy (compare `on` fst) d)

-- >>> raw (norm (sum <$> dice 2))
-- [(2,1 % 36),(3,1 % 18),(4,1 % 12),(5,1 % 9),(6,5 % 36),(7,1 % 6),(8,5 % 36),(9,1 % 9),(10,1 % 12),(11,1 % 18),(12,1 % 36)]

--
distinctDice :: Int -> Dist [Int]
distinctDice 0 = return []
distinctDice n =
    do d <- uniform [1..6]
       ds <- distinctDice (n - 1)
       guard (d `notElem` ds)
       return (d : ds)

-- >>> raw (distinctDice 2)
-- [([1,2],1 % 36),([1,3],1 % 36),([1,4],1 % 36),([1,5],1 % 36),([1,6],1 % 36),([2,1],1 % 36),([2,3],1 % 36),([2,4],1 % 36),([2,5],1 % 36),([2,6],1 % 36),([3,1],1 % 36),([3,2],1 % 36),([3,4],1 % 36),([3,5],1 % 36),([3,6],1 % 36),([4,1],1 % 36),([4,2],1 % 36),([4,3],1 % 36),([4,5],1 % 36),([4,6],1 % 36),([5,1],1 % 36),([5,2],1 % 36),([5,3],1 % 36),([5,4],1 % 36),([5,6],1 % 36),([6,1],1 % 36),([6,2],1 % 36),([6,3],1 % 36),([6,4],1 % 36),([6,5],1 % 36)]

-- >>> raw (sum <$> distinctDice 2)
-- [(3,1 % 36),(4,1 % 36),(5,1 % 36),(6,1 % 36),(7,1 % 36),(3,1 % 36),(5,1 % 36),(6,1 % 36),(7,1 % 36),(8,1 % 36),(4,1 % 36),(5,1 % 36),(7,1 % 36),(8,1 % 36),(9,1 % 36),(5,1 % 36),(6,1 % 36),(7,1 % 36),(9,1 % 36),(10,1 % 36),(6,1 % 36),(7,1 % 36),(8,1 % 36),(9,1 % 36),(11,1 % 36),(7,1 % 36),(8,1 % 36),(9,1 % 36),(10,1 % 36),(11,1 % 36)]

-- >>> sum (map snd (raw (sum <$> distinctDice 2)))
-- 5 % 6


-- >>> norm (sum <$> distinctDice 2)
-- [(3,1 % 15),(4,1 % 15),(5,2 % 15),(6,2 % 15),(7,1 % 5),(8,2 % 15),(9,2 % 15),(10,1 % 15),(11,1 % 15)]

--- Monte Hall problem

doors = [1..3]

stay = do prize <- uniform doors
          picked <- uniform doors
          return (prize == picked)

-- >>> norm stay
-- [(False,2 % 3),(True,1 % 3)]

switch = do prize <- uniform doors
            picked <- uniform doors
            revealed <- uniform [x | x <- [1..3], x `notElem` [prize, picked]]
            newPick <- uniform [x | x <- [1..3], x `notElem` [picked, revealed]]
            return (newPick == prize)

-- >>> norm switch
-- [(False,1 % 3),(True,2 % 3)]

--- "Infinite" distribution

streak n = do c <- uniform [True, False]
              if c then return n else streak (n + 1)

-- >>> take 40 $ raw (streak 0)
-- [(0,1 % 2),(1,1 % 4),(2,1 % 8),(3,1 % 16),(4,1 % 32),(5,1 % 64),(6,1 % 128),(7,1 % 256),(8,1 % 512),(9,1 % 1024),(10,1 % 2048),(11,1 % 4096),(12,1 % 8192),(13,1 % 16384),(14,1 % 32768),(15,1 % 65536),(16,1 % 131072),(17,1 % 262144),(18,1 % 524288),(19,1 % 1048576),(20,1 % 2097152),(21,1 % 4194304),(22,1 % 8388608),(23,1 % 16777216),(24,1 % 33554432),(25,1 % 67108864),(26,1 % 134217728),(27,1 % 268435456),(28,1 % 536870912),(29,1 % 1073741824),(30,1 % 2147483648),(31,1 % 4294967296),(32,1 % 8589934592),(33,1 % 17179869184),(34,1 % 34359738368),(35,1 % 68719476736),(36,1 % 137438953472),(37,1 % 274877906944),(38,1 % 549755813888),(39,1 % 1099511627776)]

--- Now would be a good time to switch to `Float` for probabilities

shape :: (Float -> Float) -> [a] -> Dist a
shape f as = Dist (zip as (map scale ys))
    where incr    = 1 / fromIntegral (length as - 1)
          xs      = take (length as) (iterate (incr +) 0)
          ys      = map f xs
          scale y = y / sum ys

normalCurve :: Float -> Float -> Float -> Float
normalCurve mean stddev x = 1 / sqrt (2 * pi) * exp (-1/2 * u^2)
    where u = (x - mean) / stddev

normal :: [a] -> Dist a
normal = shape (normalCurve 0.5 0.25)

-- >>> raw (normal [1..20]) !! 0
-- (1,1.1777931e-2)

-- >>> raw (normal [1..20]) !! 10
-- (11,8.654697e-2)

choices :: [(Probability, Dist a)] -> Dist a
choices pds = Dist (concatMap squash pds)
    where squash (p, Dist d) = [(a, p * q) | (a, q) <- d]

data Tree = Alive Int | Hit Int | Fallen
  deriving (Eq, Ord, Show)

yearly (Alive h) = choices [ (0.9,  uniform [Alive (h + i) | i <- [1..4]])
                           , (0.04, return (Hit h))
                           , (0.06, return Fallen) ]
yearly t         = return t

q = 1

-- >>> raw (yearly (Alive 1))
-- [(Alive 2,0.225),(Alive 3,0.225),(Alive 4,0.225),(Alive 5,0.225),(Hit 1,4.0e-2),(Fallen,6.0e-2)]

-- >>> norm (return (Alive 0) >>= yearly >>= yearly)
-- [(Alive 2,5.0625004e-2),(Alive 3,0.10125001),(Alive 4,0.15187502),(Alive 5,0.20250002),(Alive 6,0.15187502),(Alive 7,0.10125001),(Alive 8,5.0625004e-2),(Hit 0,4.0000007e-2),(Hit 1,9.0000015e-3),(Hit 2,9.0000015e-3),(Hit 3,9.0000015e-3),(Hit 4,9.0000015e-3),(Fallen,0.114000015)]

iterateM :: Monad m => Int -> (a -> m a) -> a -> m a
iterateM 0 _ x = return x
iterateM n f x = f x >>= iterateM (n - 1) f

trees :: Int -> Int -> Dist Int
trees n k =
    do ts <- sequence (replicate n (iterateM k yearly (Alive 0)))
       return (length (filter alive ts))
    where alive (Alive _) = True
          alive _         = False


main :: IO ()
main = return ()
