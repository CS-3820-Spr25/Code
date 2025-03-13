module Problems3 where

import Data.Char (ord)

{-------------------------------------------------------------------------------

CS:3820 Spring 2025 Problem Set 3
=================================

The problems in this problem set are focused on recursion: iteration over
numeric and list types.  As before, you should consider the type signature as
part of the problem specification, so you should not change it.

A technical note: you are likely to write at least one function that runs
forever.  If you test your code locally using `cabal run Test`, you will have
to interrupt `cabal` using Ctrl + C.  Note that in this case Cabal will still
print a `Cases: 31 Tried: N Errors: 0 Failures: 0` line.   However, since
the tests did not finish the test would still be counted as a failure.
Always check the Github autograder!

Sometimes the problem specification might be incomplete.  Ask yourself whether
all cases are clearly defined, and whether your solution makes assumptions
about any undefined cases.  Often it is helpful to also have a look at the
unit tests in `Tests.hs` to clarify any ambiguities.
-------------------------------------------------------------------------------}

--------------------------------------------------------------------------------
-- 1. Semi-factorial.
--
-- The semi-factorial of n, written n!!, consists of the product of every
-- *other* number from n down to 1.  For example:
--
--    5!! = 5 * 3 * 1 = 15
--    4!! = 4 * 2 = 8
--
-- Contrast the factorial, which is the product of *every* number from n down to
-- 1:
--
--    5! = 5 * 4 * 3 * 2 * 1 = 120
--
-- The factorial has an easy recursive definition:
--
--    0! = 1
--    n! = n * (n - 1)!
--
-- Your task is to develop a recursive definition of the semi-factorial.

semifact :: Int -> Int
semifact n
  | n <= 1    = 1
  | otherwise = n * semifact (n - 2)

--------------------------------------------------------------------------------
-- 2. The Collatz sequence
--
-- The Collatz sequence is given as follows:
--
--   1. If the current number n is 1, the sequence ends
--   2. If the current number n is even, the sequence continues with n/2
--   3. If the current number n is odd, the sequence continues with 3n+1
--
-- For example, the Collatz sequence starting from 4 is 4, 2, 1.  The Collatz
-- sequence starting from 7 is 7,22,11,34,17,52,26,13,40,20,10,5,16,8,4,2,1.
--
-- Your tasks is to write a function that, given a starting point, returns the
-- Collatz sequence from that starting point, as a list.  You need to know two
-- more things about lists to write this function:
--
--   * A constant list of elements x1, x2, x3 is written [x1, x2, x3].  In
--     particular, the constant list with no elements is written [].
--
--   * To prepend a *single* element onto a list, use the : operator.  For
--     example, `1 : [2,3,4]` is the same list as `[1,2,3,4]`.

collatz :: Int -> [Int]
collatz n
  | n == 1 = [n]
  | even n = n : collatz (n `div` 2)
  | odd n = n : collatz (3 * n + 1)


{-------------------------------------------------------------------------------

The next few problems all deal with lists.  One way to get access to lists is
via *pattern matching*: a list is either the empty list, writen `[]`, or it's a
"cons" cell, written `x : xs` (or whatever variables you prefer...)
Alternatively, there are a couple of functions for manipulating lists:

  * the `null` function returns `True` for an empty list, and `False` for a
    non-empty list

  * The `head` function returns the first element of a non-empty list, and
    crashes if applied to an empty list.

  * The `tail` function returns everything *but* the first element of a
    non-empty list, and crashes if applied to an empty list.

-------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------

   3. Let's begin with a simple function pattern matching on lists.
  
   The **Collatz Conjecture** asserts that, for any positive integer `n`, the
   collatz sequence starting with `n` will terminate at 1. Write a recursive
   function that verifies if a given input sequence has 1 as its last
   element. (The pattern matching cases of this function have been given to you
   below. In each case, return True, False, or recurse.)
  
-------------------------------------------------------------------------------}

endsInOne :: [Int] -> Bool
endsInOne []  = False
endsInOne [1] = True
endsInOne (x : xs) = endsInOne xs

-- If the Collatz Conjecture is true, what should `endsInOne (collatz n)`
-- equal (for all positive n)?

--------------------------------------------------------------------------------
-- 4. Write a function which returns the even-indexed elements of a list---that
--    is to say, the second, fourth, sixth, and so forth.  For example,
--    `evenIndexes ['a','b','c','d']` should return ['b','d']

evenIndexes :: [a] -> [a]
evenIndexes (_ : x : xs) = x : evenIndexes xs
evenIndexes _            = []

--------------------------------------------------------------------------------
-- 5. Write a function which, given a list [x1, x2, x3, x4, ...], computes 0 -
--    x1 + x2 - x3 + x4 - ....  Given an empty list, you should return 0.

alternating :: [Int] -> Int
alternating xs = sum (evenIndexes xs) - sum (oddIndexes xs)
  where oddIndexes [] = []
        oddIndexes (x : xs) = x : evenIndexes xs


{-------------------------------------------------------------------------------

The next two functions deal with the subset sum problem.  This problem is to
solve the question: given a list of integers L := [x1, x2, ..., xn] and a target
T is there sublist M such that the (sum M) is T.

Here is a naive recursive algorithm that solve this problem described as
imperative pseudo code:

SubsetSum(L, T):
  if T = 0:
    return True
  else if T < 0 or L = []
    return False
  else
    x <- head L
    L' <- tail L
    with ← SubsetSum(L', T − x)
    wout ← SubsetSum(L', T )
    return (with or wout)

This algorithm works by iterating over the list and at each element
guessing whether it is included in the sum (the with case), or whether it
is not included (the wout case).  To explore both guesses, it performs two
recursive calls.

-------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------

6. Translate this pseudo code into Haskell.  To do so, write a function
   subsetsum that expects a list and a target number and returns a boolean
   truth value.

   For example,
     subsetsum [1, 2, 3] 5 should evaluate to True (2 + 3)
     subsetsum [1, 2, 5] 4 should evaluate to False
-------------------------------------------------------------------------------}

subsetsum :: [Int] -> Int -> Bool
subsetsum _ 0  = True
subsetsum [] _ = False
subsetsum (x:xs) t
  | t < 0 = False
  | otherwise = (subsetsum xs (t - x)) || (subsetsum xs t)

{-------------------------------------------------------------------------------

7. We now would like to know which elements of the list must be summed to
   reach the target T.  We want to represent this as a list of booleans.
   This list should have the same length as the input list L and contain
   a "True" if an number is picked, and "False" otherwise.

   However, the algorithm can also fail if there is no subset that sums to
   T.  Hence, insted of returning a [Bool], we return a Maybe [Bool].
   A return value of Nothing indicates that there is no subset that sums
   to T.

   subsetsumResult [1, 2, 3] 5 should evaluate to Just [False, True, True]
   subsetsumResult [1, 2, 5] 4 should evaluate to Nothing
-------------------------------------------------------------------------------}

subsetsumResult :: [Int] -> Int -> Maybe [Bool]
subsetsumResult []     0   = Just []
subsetsumResult (x:xs) 0   = attachMaybe False (subsetsumResult xs 0)
  where
    attachMaybe :: a -> Maybe [a] -> Maybe [a]
    attachMaybe _ Nothing   = Nothing
    attachMaybe x (Just xs) = Just (x:xs)
subsetsumResult []     _   = Nothing
subsetsumResult (x:xs) t
  | t < 0 = Nothing
  | otherwise = subsetsumAttach (subsetsumResult xs (t - x)) (subsetsumResult xs t)
      where
        subsetsumAttach :: Maybe [Bool] -> Maybe [Bool] -> Maybe [Bool]
        subsetsumAttach (Just bs) _ = Just (True:bs)
        subsetsumAttach _ (Just bs) = Just (False:bs)
        subsetsumAttach _ _ = Nothing

{-------------------------------------------------------------------------------

8. A very convenient feature of Haskell are Lambda expressions.  Lambda
   expressions make it possible to introduce functions without giving them a
   name.

   As an example, let's say we want to define a function that adds two to the
   argument.  We can do this by writing `(\x -> x + 2)`.  The backslash
   starts the Lambda expression (\ looks a bit like λ).  Then to the left of
   the `->` is the list of arguments, and to the right is the expression that
   defines the function.  It is also possible to use more than one argument.
   Consider, `(\x y -> 2 * x + y)`.

   Lambda expressions are especially useful to provide functions to higher
   order functions.  For example, `map (\ x -> show (2 * x))` is the function
   that doubles each element of a list and shows the result as a String.
   `map (\ x -> show (2 * x)) [1,2,3]` evaluates to `["2", "4", "6"]`.

   Read the definition of `mapNeighbors` and give a lambda expression such
   that using this expression with `mapNeighbor` returns a list of values and
   their difference to the next value.

   For example:
   mapNeighbors myLambda 0 [1,5,2] = [(1, 4), (5, -3), (2, -2)]
-------------------------------------------------------------------------------}

mapNeighbors :: (a -> a -> b) -> a -> [a] -> [b]
mapNeighbors f x []         = []
mapNeighbors f x [y]        = [f y x]
mapNeighbors f x (y1:y2:ys) = (f y1 y2) : (mapNeighbors f x (y2:ys))

myLambda :: Int -> Int -> (Int, Int)
myLambda = (\x y -> (x, y - x))
