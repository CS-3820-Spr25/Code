{-# LANGUAGE PatternGuards #-}
module Problems10 (module Problems10) where

{-------------------------------------------------------------------------------

CS:3820 Spring 2025 Problem Set 10
==================================

This problem set continues our exploration of big-step semantics for
call-by-value functional programming languages.  The novelty now is that we're
adding sum types.  Over the course of this assignment, you'll implement two
approaches to sum types, one based on substitution and another based on
environments.

One way to think about sum types is as generalizations of Booleans.  A Boolean
value represents a binary choice: it can either be True or False.  A conditional
inspects a Boolean value, and behaves one way if it's True and another way if
it's False.  Sum types generalize this idea by carrying additional data along
with the binary choice.  A value of sum type is either `OnLeft v`, where `v` is
some value, or its `OnRight w`, where (again) `w` is some value.  A case
statement inspects a value of sum type, and behaves one way if it's `OnLeft v`,
and another if it's `OnRight w`; in either case, the behavior has access to the
carried value `v` or `w`.

Another way to think about sum types is that they're the simplest interesting
example of a Haskell data type---one with two constructors---and that a case
statement is pattern matching custom-built to this type.

It's probably helpful to have some examples.  I'll start by giving them in
pseudo-Haskell, and then we'll see how they're represented in our embedded
language.

Here's a function that uses a sum to decide whether to increment or decrement:

    \x -> case x of OnLeft y -> y + 1; OnRight z -> z + (-1)

Now, suppose we applied this to a suitable argument; we might expect small-step
reduction sequences like the following:

    (\x -> case x of OnLeft y -> y + 1; OnRight z -> z + (-1)) (OnLeft 3)
  -->
    case (OnLeft 3) of OnLeft y -> y + 1; OnRight z -> z + (-1)
  -->
    3 + 1
  -->
    4

Notice how the second step combines two ideas: we choose between the left and
right branches, and we substitute for the variable `y`.  Here's another
small-step reduction sequence:

    (\x -> case x of OnLeft y -> y + 1; OnRight z -> z + (-1)) (OnRight (1 + 2))
  -->
    (\x -> case x of OnLeft y -> y + 1; OnRight z -> z + (-1)) (OnRight 3)
  -->
    case (OnRight 3) of OnLeft y -> y + 1; OnRight z -> z + (-1)
  -->
    3 + (-1)
  -->
    2
    
We're doing call-by-value reduction, so we have to start out by reducing
`OnRight (1 + 2)` to a value.  Once we've done that, we can substitute for `x`
and proceed.

In this example, the two branches of the case statement have different variable
names, but that isn't necessary:

    (\x -> case x of OnLeft y -> y + 1; OnRight y -> y + (-1)) (OnLeft 3)
  -->
    case (OnLeft 3) of OnLeft y -> y + 1; OnRight y -> y + (-1)
  -->
    3 + 1
  -->
    4

We also don't need to have the same type on either side of a sum.  Here's a
function that operates on a sum that's either an integer value or an integer
function:

    \x -> case x of OnLeft f -> f 1; OnRight y -> y

And two sample small-step reductions.  Number 1:

    (\x -> case x of OnLeft f -> f 1; OnRight y -> y) (OnLeft (\y -> y + 1))
  -->
    case (OnLeft (\y -> y + 1)) of OnLeft f -> f 1; OnRight y -> y
  -->
    (\y -> y + 1) 1
  -->
    1 + 1
  --> 2

And number 2:

    (\x -> case x of OnLeft f -> f 1; OnRight y -> y) (OnRight 3)
  -->
    case (OnRight 3) of OnLeft f -> f 1; OnRight y -> y
  -->
    3

-------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------

Here's the embedded version of the language above:

-------------------------------------------------------------------------------}

type Name = String
data Expr = Const Int | Plus Expr Expr | Times Expr Expr 
          | Var Name | Lam Name Expr | App Expr Expr
          | OnLeft Expr | OnRight Expr | Case Expr Name Expr Name Expr
  deriving (Eq, Show)

{-------------------------------------------------------------------------------

The arithmetic and function cases are as you've seen them before.  `OnLeft` and
`OnRight` should be self-explanatory.  The `Case` constructor takes 5 arguments.
The first is the expression to examine.  The next two are the "OnLeft" branch: a
variable for the contents, and the body of the branch.  The final two are the
"OnRight" branch, similarly.

Concretely, to embed this expression:

    case x of OnLeft y -> y + 1; OnRight z -> z + (-1)

we would use:

    Case (Var "x")
         "y" (Plus (Var "y") (Const 1))
         "z" (Plus (Var "z") (Const (-1)))

or for this expression:

    case x of OnLeft f -> f 1; OnRight y -> y

we would use:

    Case (Var "x")
         "f" (App (Var "f") (Const 1))
         "y" (Var "y")

-------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------

Problems 1 - 2
--------------

For the first part of this problem, we're going to build a substitution-based
big-step semantics.  Before we can write the interpreter itself, we'll need a
notion of values and a substitution function.  Here's our definition of values:

-------------------------------------------------------------------------------}

data ValS = SInt Int | SLam Name Expr | SLeft ValS | SRight ValS
  deriving (Eq, Show)

{-------------------------------------------------------------------------------

Your task is to write the substitution function, with the following type.  There
are a couple of things to keep in mind when writing your function.

* You're substituting *values*---that is, the results of substitution---into
  *expressions*.  Because we've defined a separate type for values, you'll need
  to write a conversion function from values back to expressions.

* Because `case` statements bind new variables for each branch---that is to say, in
      
      case L of OnLeft x -> M; OnRight y -> N

  the variable x is new in branch M, and the variable y is new in branch N---the
  same rules about variable shadowing apply to case statements that apply to
  lambdas.  For example, considering the following substitution:

      (case L of OnLeft x -> M; OnRight y -> N)[P/x]

  where L, M, N, and P are arbitrary expressions.  We'll substitute P for x in
  L---because that's not inside any binder---and in N---because the bound
  variable there is different from `x`, but *not* inside M.  That is, the above
  will be equal to

      case L[P/x] of OnLeft x -> M; OnRight y -> N[L/x]

Your solution will be assessed in two parts.  Problem 1 is the arithmetic and
functional constructs (Const, Plus, Times, Var, App, Lam); Problem 2 is the sum
constructs (OnLeft, OnRight, Case).

-------------------------------------------------------------------------------}  

substitute :: Name -> ValS -> Expr -> Expr
substitute x m (Const i) = Const i
substitute x m (Plus n1 n2) = Plus (substitute x m n1) (substitute x m n2)
substitute x m (Times n1 n2) = Times (substitute x m n1) (substitute x m n2)
substitute x m (Var y) 
  | x == y = exprOf m
  | otherwise = Var y
  where exprOf (SInt i) = Const i
        exprOf (SLam w m) = Lam w m
        exprOf (SLeft v) = OnLeft (exprOf v)
        exprOf (SRight v) = OnRight (exprOf v)
substitute x m (Lam y n)
  | x == y = Lam y n
  | otherwise = Lam y (substitute x m n)
substitute x m (App n1 n2) = App (substitute x m n1) (substitute x m n2)
substitute x m (OnLeft n) = OnLeft (substitute x m n)
substitute x m (OnRight n) = OnRight (substitute x m n)
substitute x m (Case l y1 n1 y2 n2) =
  Case (substitute x m l) 
       y1 (if x == y1 then n1 else substitute x m n1) 
       y2 (if x == y2 then n2 else substitute x m n2)

{-------------------------------------------------------------------------------

Problems 3 - 5
--------------

Next, you should write the evaluation function itself.  Again, a couple of
notes:

* Our evaluation strategy is *call-by-value*: that is to say, you should fully
  evaluate arguments to functions *before* substituting into the function body.
  (This should actually be enforced by the type of your substitution operator.)

* Your evaluation function should *never* crash; when given an expression that
  doesn't reduce to a value, such case

      case 1 of OnLeft x -> x; OnRight y -> y + 1

  You should return `Nothing`.

Your solution will be evaluated in three parts.  Problem 3 is only the
arithmetic operations; problem 4 also includes the functional features (Var,
App, and Lam), and problem 5 adds OnLeft, OnRight, and Case.  

-------------------------------------------------------------------------------}

evalS :: Expr -> Maybe ValS
evalS (Const i) = Just (SInt i)
evalS (Plus n1 n2)
  | Just (SInt i1) <- evalS n1, Just (SInt i2) <- evalS n2 = Just (SInt (i1 + i2))
  | otherwise = Nothing
evalS (Times n1 n2)
  | Just (SInt i1) <- evalS n1, Just (SInt i2) <- evalS n2 = Just (SInt (i1 * i2))
  | otherwise = Nothing
evalS (Var x) = Nothing
evalS (Lam x m) = Just (SLam x m)
evalS (App m n)
  | Just (SLam x m') <- evalS m, Just w <- evalS n = evalS (substitute x w m')
  | otherwise = Nothing
evalS (OnLeft m) = fmap SLeft (evalS m)
evalS (OnRight m) = fmap SRight (evalS m)
evalS (Case l y1 m1 y2 m2)
  | Just (SLeft v) <- mv = evalS (substitute y1 v m1)
  | Just (SRight v) <- mv = evalS (substitute y2 v m2)
  | otherwise = Nothing 
  where mv = evalS l


{-------------------------------------------------------------------------------

Problems 6 - 8
--------------

Another approach to big-step semantics is to use an *environment*.  You can view
the environment as an accumulated substitution, tracking all the different
substitutions you would have made as you evaluate an expression.

The significant additional complication that arises with an environment-based
approach is that we need to associate function bodies with the environments in
which they were *defined*, not the environment in which they end up being
*used*.  This means that we have a new type of values, in which *closures*
combine functions and environments.

You may want to review the lecture notes on closures, particularly lecture 8C.

As in the previous evaluation function, your evaluation function should *never*
crash, instead returning `Nothing` for invalid expressions.

Your solution will be evaluated in three parts.  Problem 6 is only the
arithmetic operations; problem 7 also includes the functional features (Var,
App, and Lam), and problem 8 adds OnLeft, OnRight, and Case.  


-------------------------------------------------------------------------------}

type Env = [(Name, ValC)]
data ValC = CInt Int | CClos Env Name Expr | CLeft ValC | CRight ValC
  deriving (Eq, Show)

evalC :: Env -> Expr -> Maybe ValC
evalC _ (Const i) = Just (CInt i)
evalC h (Plus n1 n2)
  | Just (CInt i1) <- evalC h n1, Just (CInt i2) <- evalC h n2 = Just (CInt (i1 + i2))
evalC h (Times n1 n2)
  | Just (CInt i1) <- evalC h n1, Just (CInt i2) <- evalC h n2 = Just (CInt (i1 * i2))
evalC h (Var x)
  | Just v <- lookup x h = Just v 
evalC h (Lam x m) = Just (CClos h x m)
evalC h (App m n) 
  | Just (CClos h' x m') <- evalC h m, Just v <- evalC h n = evalC ((x, v) : h') m'
evalC h (OnLeft m) = fmap CLeft (evalC h m)
evalC h (OnRight m) = fmap CRight (evalC h m)
evalC h (Case l y1 m1 y2 m2) 
  | Just (CLeft v) <- mv = evalC ((y1, v) : h) m1
  | Just (CRight v) <- mv = evalC ((y2, v) : h) m2
  where mv = evalC h l  
evalC _ _ = Nothing  
