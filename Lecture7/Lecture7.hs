{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
module Lecture7 (module Lecture7) where

{-------------------------------------------------------------------------------

Lecture 7
=========

Our goal is to explore big-step and small-step semantics by realizing them in
Haskell.  We need a language to study, here including both arithmetic and pair
operations.

-------------------------------------------------------------------------------}

data Expr = Const Int | Plus Expr Expr | Times Expr Expr | Negate Expr
          | Pair Expr Expr | Fst Expr | Snd Expr
  deriving Show

-- Toy examples, like this one, always have some goals in mind; here, I wanted
-- to have both binary and unary operations, and two types.  Of course, the
-- `Negate` operation isn't *actually* necessary; we could just multiply by -1.

{-------------------------------------------------------------------------------

Reduction ends when we reach an expression in *simplest* form; that is to say,
when we reach an expression that doesn't have any more computation we could do.
We can write a Haskell function that identifies such expressions:

-------------------------------------------------------------------------------}

isValue :: Expr -> Bool
isValue (Const _) = True
isValue (Pair m n) = isValue m && isValue n
    -- This case is a little subtle: unlike constants, not *all* pairs are
    -- values; instead, pairs *of values* are values.  The pair `Pair (Plus 1 2)
    -- (Const 3)`, on the other hand, could still reduce further.
isValue _ = False

{-------------------------------------------------------------------------------

Big-step semantics
------------------

First, we'll write a big-step semantics for expressions.  Remember that a
big-step semantics reaches the simplest form in a single ("big") step.  We'll
start out by just writing this as an `Expr -> Expr` function, but in which we
want to maintain the invariant that we always produce a value.

-------------------------------------------------------------------------------}

bigStep :: Expr -> Expr
bigStep (Const i) = Const i
  -- Constants are already in simplest form
bigStep (Plus m n) = Const (asConst (bigStep m) + asConst (bigStep n))
  -- If we're going to add `m` and `n`, we need to know:
  --   * The constant to which `m` reduces (call it i)
  --   * The constant to which `n` reduces (call it j)  
  -- and then we can produce the constant `i + j`.  The helper function
  -- `asConst` picks the constant out of the recursive invocations of `bigStep`
bigStep (Times m n) = Const (asConst (bigStep m) * asConst (bigStep n))  
bigStep (Negate m) = Const (negate (asConst (bigStep m)))
  -- Similar reasoning to `Plus`
bigStep (Pair m n) = Pair (bigStep m) (bigStep n)  
  -- Pairs may not be in simplest form, but we don't have any requirements on
  -- the kinds of expressions to which the components reduce.`
bigStep (Fst m) = fst (asPair (bigStep m))
  -- To get the first component from `m`, we need to know to which pair `m`
  -- reduces.
bigStep (Snd m) = snd (asPair (bigStep m))


-- Helper functions

asConst :: Expr -> Int
asConst (Const i) = i
asConst e = error ("Expected " ++ show e ++ " to be an integer constant")

asPair :: Expr -> (Expr, Expr)
asPair (Pair m n) = (m, n)
asPair e = error ("Expected " ++ show e ++ " to be a pair constant")

{-------------------------------------------------------------------------------

Two claims about this function.

First: if `bigStep m` results in `n`, then `isValue n`.  


-------------------------------------------------------------------------------}




-- Claim: bigStem m == m'  ==>  isValue m'

data Value = VInt Int | VPair Value Value
  deriving Show

intv :: Value -> Int
intv (VInt i) = i
intv _ = error "int expected"

pairv :: Value -> (Value, Value)
pairv (VPair v w) = (v, w)
pairv _ = error "pair expected"

bigStep' :: Expr -> Value
bigStep' (Const i) = VInt i
bigStep' (Plus m n) = VInt (intv (bigStep' m) + intv (bigStep' n))
bigStep' (Times m n) = VInt (intv (bigStep' m) * intv (bigStep' n))
bigStep' (Negate m) = VInt (negate (intv (bigStep' m)))
bigStep' (Pair m n) = VPair (bigStep' m) (bigStep' n)
bigStep' (Fst m) = fst (pairv (bigStep' m))
bigStep' (Snd m) = snd (pairv (bigStep' m))

smallStep :: Expr -> Expr
smallStep (Const i) = error "no step"
smallStep (Plus (Const i) (Const j)) = Const (i + j)
smallStep (Plus m n)
  | isValue m = Plus m (smallStep n)
  | otherwise = Plus (smallStep m) n
smallStep (Times (Const i) (Const j)) = Const (i * j)
smallStep (Times m n)
  | isValue m = Times m (smallStep n)
  | otherwise = Times (smallStep m) n
smallStep (Negate (Const i)) = Const (negate i)
smallStep (Negate m) = Negate (smallStep m)
smallStep (Pair m n)
  | isValue m = Pair m (smallStep n)
  | otherwise = Pair (smallStep m) n
smallStep (Fst (Pair m n)) = m
smallStep (Fst m) = Fst (smallStep m)
smallStep (Snd (Pair m n)) = n
smallStep (Snd m) = Snd (smallStep m)

smallSteps :: Expr -> [Expr]
smallSteps m
  | isValue m = [m]
  | otherwise = m : smallSteps (smallStep m)

try :: Maybe a -> (a -> b) -> Maybe b -> Maybe b
try m f z = maybe z (Just . f) m

binaryCong :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Maybe Expr
binaryCong f m n = 
  try (smallStep' m)
    (\m' -> f m' n)
    (try (smallStep' n)
         (\n' -> f m n')
         Nothing)

unaryCong :: (Expr -> Expr) -> Expr -> Maybe Expr
unaryCong f m = try (smallStep' m) f Nothing

smallStep' :: Expr -> Maybe Expr
smallStep' (Const _) = Nothing
smallStep' (Plus (Const i) (Const j)) = Just (Const (i + j))
smallStep' (Plus m n) = binaryCong Plus m n 
smallStep' (Times (Const i) (Const j)) = Just (Const (i * j))
smallStep' (Times m n) = binaryCong Times m n
smallStep' (Negate (Const i)) = Just (Const (negate i))
smallStep' (Negate m) = unaryCong Negate m
smallStep' (Pair m n) = binaryCong Pair m n
smallStep' (Fst (Pair m n)) = Just m
smallStep' (Fst m) = unaryCong Fst m
smallStep' (Snd (Pair m n)) = Just n
smallStep' (Snd m) = unaryCong Snd m

smallSteps' :: Expr -> [Expr]
smallSteps' m = 
  case smallStep' m of
    Nothing -> [m]
    Just m' -> m : smallSteps' m'

-- examples
e, e' :: Expr
e = Plus (Plus (Const 3) (Const 4)) (Snd (Pair (Negate (Const 1)) (Negate (Const 2))))
e' = Plus (Plus (Const 3) (Pair (Const 4) (Const 3))) (Snd (Pair (Negate (Const 1)) (Negate (Const 2))))


main :: IO ()
main = return ()
