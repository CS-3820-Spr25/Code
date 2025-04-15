{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
module Lecture8A (module Lecture8A) where

import Lecture8Common

type Name = String
data Expr = Const Int | Plus Expr Expr | Times Expr Expr
          | Var Name | Lam Name Expr | App Expr Expr
  deriving (Eq, Show)

(@) :: Expr -> Expr -> Expr
(@) = App
infixl 9 @

e1, e2, e3, e4, e5 :: Expr

--   (\x -> x + x) 1
e1 = Lam "x" (Plus (Var "x") (Var "x")) @ Const 1

--   (\x -> x + x) (1 + 2)
e2 = Lam "x" (Plus (Var "x") (Var "x")) @ Plus (Const 1) (Const 2)

-- (\x -> (\y -> x + y)) 1 2 
e3 = Lam "x" (Lam "y" (Plus (Var "x") (Var "x"))) @ Const 1 @ Const 2

-- (\f -> (\x -> f x)) (\y -> y + 1) 2
e4 = Lam "f" (Lam "x" (App (Var "f") (Var "x"))) @ Lam "y" (Plus (Var "y") (Const 1)) @ Const 2

-- (\x -> \x -> x) 1 2
e5 = Lam "x" (Lam "x" (Var "x")) @ Const 1 @ Const 2

omega :: Expr
-- (\x -> x x) (\x -> x x)
omega = Lam "x" (Var "x" @ Var "x") @ Lam "x" (Var "x" @ Var "x")

substitute :: Name -> Expr -> Expr -> Expr
substitute x m (Const i) = Const i
substitute x m (Plus n1 n2) = Plus (substitute x m n1) (substitute x m n2)
substitute x m (Times n1 n2) = Times (substitute x m n1) (substitute x m n2)
substitute x m (Var y) 
  | x == y = m
  | otherwise = Var y
substitute x m (Lam y n)                                 
  | x == y = Lam y n
  | otherwise = Lam y (substitute x m n)
substitute x m (App n1 n2) = App (substitute x m n1) (substitute x m n2)

binaryCongCBN = binaryCongGeneric smallStepCBN

smallStepCBN :: Expr -> Maybe Expr
smallStepCBN (Const _) = Nothing
smallStepCBN (Plus (Const i) (Const j)) = Just (Const (i + j))
smallStepCBN (Plus m n) = binaryCongCBN Plus m n 
smallStepCBN (Times (Const i) (Const j)) = Just (Const (i * j))
smallStepCBN (Times m n) = binaryCongCBN Times m n
smallStepCBN (Var _) = Nothing
smallStepCBN (Lam _ _) = Nothing
smallStepCBN (App (Lam x m) n) = Just (substitute x n m)
smallStepCBN (App m n) = binaryCongCBN App m n

smallStepsCBN :: Expr -> [Expr]
smallStepsCBN = untilNothing smallStepCBN

binaryCongCBV = binaryCongGeneric smallStepCBV                        

smallStepCBV :: Expr -> Maybe Expr
smallStepCBV (Const _) = Nothing
smallStepCBV (Plus (Const i) (Const j)) = Just (Const (i + j))
smallStepCBV (Plus m n) = binaryCongCBV Plus m n 
smallStepCBV (Times (Const i) (Const j)) = Just (Const (i * j))
smallStepCBV (Times m n) = binaryCongCBV Times m n
smallStepCBV (Var _) = Nothing
smallStepCBV (Lam _ _) = Nothing
smallStepCBV (App (Lam x m) n) =
  try (smallStepCBV n) (App (Lam x m)) (Just (substitute x n m))
smallStepCBV (App m n) = binaryCongCBV App m n

smallStepsCBV :: Expr -> [Expr]
smallStepsCBV = untilNothing smallStepCBV

--

