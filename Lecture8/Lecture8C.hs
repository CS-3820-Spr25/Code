module Lecture8C (module Lecture8C) where


type Name = String
data Expr = Const Int | Plus Expr Expr | Times Expr Expr
          | Var Name | Lam Name Expr | App Expr Expr 
  deriving (Eq, Show)
data Value env = VInt Int | VClosure env Name Expr
  deriving (Eq, Show)
data EnvCBV = EV [(Name, Value EnvCBV)]
  deriving (Eq, Show)

type ValueCBV = Value EnvCBV


(@) :: Expr -> Expr -> Expr
(@) = App
infixl 9 @

e1 = Lam "x" (Plus (Var "x") (Var "x")) @ Const 1

e2 = Lam "x" (Plus (Var "x") (Var "x")) @ Plus (Const 1) (Const 2)

e3 = Lam "x" (Lam "y" (Plus (Var "x") (Var "x"))) @ Const 1 @ Const 2

e4 = Lam "f" (Lam "x" (App (Var "f") (Var "x"))) @ Lam "y" (Plus (Var "y") (Const 1)) @ Const 2

e5 = Lam "x" (Lam "x" (Var "x")) @ Const 1 @ Const 2

omega :: Expr
omega = Lam "x" (Var "x" @ Var "x") @ Lam "x" (Var "x" @ Var "x")

asInt :: Maybe (Value env) -> (Int -> Maybe (Value env)) -> Maybe (Value env)
asInt (Just (VInt i)) k = k i
asInt _ _ = Nothing

asClosure :: Maybe (Value env) -> (env -> Name -> Expr -> Maybe (Value env)) -> Maybe (Value env)
asClosure (Just (VClosure h x m)) k = k h x m
asClosure _ _ = Nothing

asValue :: Maybe (Value env) -> (Value env -> Maybe (Value env)) -> Maybe (Value env)
asValue (Just v) k = k v
asValue _ _ = Nothing

bigStepCBV :: EnvCBV -> Expr -> Maybe ValueCBV
bigStepCBV _ (Const i) = Just (VInt i)
bigStepCBV h (Plus m n) = asInt (bigStepCBV h m) $ \i ->
                          asInt (bigStepCBV h n) $ \j ->
                            Just (VInt (i + j))
bigStepCBV h (Times m n) = asInt (bigStepCBV h m) $ \i ->
                           asInt (bigStepCBV h n) $ \j ->
                             Just (VInt (i + j))
bigStepCBV (EV h) (Var x) = lookup x h
bigStepCBV h (Lam x m) = Just (VClosure h x m)
bigStepCBV h (App m n) = asClosure (bigStepCBV h m) $ \(EV h') x m' ->
                         asValue (bigStepCBV h n) $ \v ->
                           bigStepCBV (EV ((x, v) : h')) m'
                        

data EnvCBN = EN [(Name, (Expr, EnvCBN))]
  deriving (Eq, Show)
type ValueCBN = Value EnvCBN

bigStepCBN :: EnvCBN -> Expr -> Maybe ValueCBN
bigStepCBN _ (Const i) = Just (VInt i)
bigStepCBN h (Plus m n) = asInt (bigStepCBN h m) $ \i ->
                          asInt (bigStepCBN h n) $ \j ->
                            Just (VInt (i + j))
bigStepCBN h (Times m n) = asInt (bigStepCBN h m) $ \i ->
                           asInt (bigStepCBN h n) $ \j ->
                             Just (VInt (i + j))
bigStepCBN (EN h) (Var x) = case lookup x h of
                           Just (e, h') -> bigStepCBN h' e
bigStepCBN h (Lam x m) = Just (VClosure h x m)
bigStepCBN h (App m n) = asClosure (bigStepCBN h m) $ \(EN h') x m' ->
                           bigStepCBN (EN ((x, (n, h)) : h')) m'
