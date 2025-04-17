module Lecture8B (module Lecture8B) where

import Lecture8Common

type Name = String
data Expr = Const Int | Plus Expr Expr | Times Expr Expr
          | Var Name | Lam Name Expr | App Expr Expr 
          | Subst Name Expr Expr   -- read Subst x m n as n[x := m]
  deriving (Eq, Show)

(@) :: Expr -> Expr -> Expr
(@) = App
infixl 9 @

e1, e2, e3, e4, e4', e5 :: Expr

e1 = Lam "x" (Plus (Var "x") (Var "x")) @ Const 1

e2 = Lam "x" (Plus (Var "x") (Var "x")) @ Plus (Const 1) (Const 2)

e3 = Lam "x" (Lam "y" (Plus (Var "x") (Var "x"))) @ Const 1 @ Const 2

e4 = Lam "f" (Lam "x" (App (Var "f") (Var "x"))) @ Lam "y" (Plus (Var "y") (Const 1)) @ Const 2

e4' = Lam "f" (Lam "x" (App (Var "f") (Plus (Var "x") (Const 1)))) @ Lam "x" (Plus (Var "x") (Const 1)) @ Const 2

e5 = Lam "x" (Lam "x" (Var "x")) @ Const 1 @ Const 2

binaryCong :: Bool -> (Expr -> Expr -> Expr) -> Expr -> Expr -> Maybe Expr
binaryCong byName = binaryCongGeneric (smallStep byName)

smallStep :: Bool -> Expr -> Maybe Expr
--
smallStep _ (Const _) = Nothing
smallStep _ (Plus (Const i) (Const j)) = Just (Const (i + j))
smallStep byName (Plus m n) = binaryCong byName Plus m n 
smallStep _ (Times (Const i) (Const j)) = Just (Const (i * j))
smallStep byName (Times m n) = binaryCong byName Times m n
--
smallStep _ (Var _) = Nothing
smallStep _ (Lam x m) = Nothing
smallStep byName (App (Lam x m) n) 
  | byName = Just (Subst x n m)
  | otherwise = try (smallStep byName n) (App (Lam x m)) (Just (Subst x n m))
smallStep byName (App m n) =
  try (smallStep byName m) (\m' -> App m' n) Nothing  
--
smallStep _ (Subst x m (Const i)) = Just (Const i)
smallStep _ (Subst x m (Plus n1 n2)) = Just (Plus (Subst x m n1) (Subst x m n2))
smallStep _ (Subst x m (Times n1 n2)) = Just (Times (Subst x m n1) (Subst x m n2))
smallStep _ (Subst x m (Var y))
  | x == y = Just m
  | otherwise = Just (Var y)
smallStep _ (Subst x m (Lam y n))
  | x == y = Just (Lam y n)
  | otherwise = Just (Lam y (Subst x m n))
smallStep _ (Subst x m (App n1 n2)) = Just (App (Subst x m n1) (Subst x m n2))
smallStep byName (Subst x m n) = 
  try (smallStep byName n) (Subst x m) Nothing

smallSteps :: Bool -> Expr -> [Expr]
smallSteps byName = untilNothing (smallStep byName)
