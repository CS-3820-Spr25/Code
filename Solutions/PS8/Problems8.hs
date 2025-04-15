{-# LANGUAGE GADTs, StandaloneDeriving #-}
module Problems8 where

{-------------------------------------------------------------------------------

CS:3820 Fall 2024 Problem Set 8
===============================

This problem continues our development of big-step semantics for simple
arithmetic languages.

The variation in this problem is that we're going to include Boolean constants
and a conditional operator:

-------------------------------------------------------------------------------}

data Expr = IConst Int | Plus Expr Expr | Times Expr Expr | Negate Expr
          | BConst Bool | If Expr Expr Expr
  deriving (Eq, Show)

-- We can still represent purely arithmetic computations:

ae1, ae2 :: Expr

ae1 = Plus (IConst 2) (IConst 3)

ae2 = Times (Plus (IConst 3) (Negate (IConst 2))) (Negate (Plus (IConst 2) (IConst 3)))

-- Purely Boolean operations aren't that interesting (although we can use
-- Haskell to be a little more interesting)

be1 :: Expr
be1 = If (BConst True) (BConst False) (BConst True)

bnot :: Expr -> Expr
band :: Expr -> Expr -> Expr

bnot m = If m (BConst False) (BConst True)
band m n = If m n (BConst False)

-- And we can put them together:

bae1, bae2 :: Expr

bae1 = If (bnot (BConst True)) (Plus (IConst 2) (IConst 3)) (Negate (Plus (IConst 2) (IConst 3)))

bae2 = Times (Plus (IConst 2) (IConst 3)) (If (band (BConst True) (bnot (BConst True))) (IConst 1) (Negate (IConst 1)))

-- Of course, not every expression is actually going to evaluate

bad :: Expr
bad = Times (Plus (IConst 2) (IConst 3)) (If (band (BConst True) (bnot (BConst True))) (IConst 1) (Negate (BConst True)))

{-------------------------------------------------------------------------------

For our big-step semantics, we'll define an explicit value type; we have both
integer and Boolean values.

-------------------------------------------------------------------------------}

data Value = VInt Int | VBool Bool
  deriving (Eq, Show)

{-------------------------------------------------------------------------------

Problems 1 & 2
--------------

Your first problem is to write a big-step evaluator for the expression type
above; that is, to write a function from `Expr` to `Maybe Value`.

The `Maybe` needs to be included as not all expressions evaluate.

Your evaluation function should *never* crash.  In particular, given expressions
like `bad` above, you should return `Nothing`, not generate a pattern matching
failure.

Problem 1 will assess your function's behavior on terms that should evaluate;
problem 2 will assess your function's behavior on terms that do not.

-------------------------------------------------------------------------------}
binop :: (Int -> Int -> Int) -> Maybe Value -> Maybe Value -> Maybe Value
binop f (Just (VInt i)) (Just (VInt j)) = Just (VInt (f i j))
binop _ _ _ = Nothing

unop :: (Int -> Int) -> Maybe Value -> Maybe Value
unop f (Just (VInt i)) = Just (VInt (f i))
unop _ _ = Nothing

branch :: Maybe Value -> Expr -> Expr -> Maybe Value
branch (Just (VBool b)) m n = if b then eval m else eval n
branch _ _ _ = Nothing

eval :: Expr -> Maybe Value
eval (IConst i) = Just (VInt i)
eval (Plus m n) = binop (+) (eval m) (eval n)
eval (Times m n) = binop (*) (eval m) (eval n)
eval (Negate m) = unop negate (eval m)
eval (BConst b) = Just (VBool b)
eval (If l m n) = branch (eval l) m n  

{-------------------------------------------------------------------------------

Problems 3 & 4
--------------

It'd be nice if we could capture which expressions will evaluate without having
to evaluate them.  (Of course, for this language, just evaluating expressions is
not difficult; but you could imagine an extension of our language with
variables, or user input, where it would not be possible to just run every
expression to see what happens.)

We'll capture this idea using a (simple) *type system*.  We'll classify
expressions by whether they're supposed to produce integer or Boolean results:

-------------------------------------------------------------------------------}

data Type = TInt | TBool
  deriving (Eq, Show)

{-------------------------------------------------------------------------------

For example, expression `ae1` above should have type `TInt`, while expression
`be1` has type `TBool`.  Of course, the whole point is that not all expressions
*should* have types; expression `bad`, above, has no type.

Your task in this problem is to write a function `typed` that computes the type
of an expression: it should return `Just TInt` if the expression will compute an
integer, `Just TBool` if it will compute a Boolean, and `Nothing` if it will not
evaluate correctly.  Your implementation should follow these rules:

* Integer constants are of type `TInt`; Boolean constants are of type `TBool`.
* Integer operations (addition, negation, multiplication) are of type `TInt`, so
  long as their arguments are of type `TInt`.
* A conditional `If l m n` is of type `t`, so long as `l` is of type `TBool`,
  and both `m` and `n` are of type `t`.  Note that in this rule, `t` may be
  *either* `TInt` *or* `TBool`.

Expressions that do not match any of these rules are not well-typed.

Your function should never crash; for ill-typed expressions, it should return
`Nothing`.

Problem 3 will assess your function's behavior on well-typed expressions; problem 4
will assess your function's behavior on ill-typed expressions.

-------------------------------------------------------------------------------}
check :: Maybe Type -> Maybe Type -> Maybe Type -> Maybe Type
check intended actual k 
  | intended == actual = k
  | otherwise = Nothing

typed :: Expr -> Maybe Type
typed (IConst _) = Just TInt
typed (Plus m n) = check (Just TInt) (typed m) $ 
                   check (Just TInt) (typed n) $ 
                   Just TInt
typed (Times m n) = check (Just TInt) (typed m) $ 
                    check (Just TInt) (typed n) $ 
                    Just TInt           
typed (Negate m) = check (Just TInt) (typed m) (Just TInt)                    
typed (BConst _) = Just TBool
typed (If l m n) = check (Just TBool) (typed l) $
                   let t = typed m in check t (typed n) t

{-------------------------------------------------------------------------------

Problem 5
---------

You should be able to convince yourself (indeed, you should be able to prove)
that if `typed m` does not evaluate to `Nothing`, then `eval m` will also not
evaluate to `Nothing`.  However, the converse property does *not* hold; there
are expressions which will evaluate, but are still ruled out by our type system.

Your task is to give an example of such an expression.

This problem will be assessed using your implementations of `eval` and `typed`.

-------------------------------------------------------------------------------}

evalsNotTyped :: Expr
evalsNotTyped = If (BConst True) (IConst 1) (Negate (BConst True))

{-------------------------------------------------------------------------------

Problem 6
---------

The idea of the `Value` type is to capture an invariant of our `eval` function.
We always *want* `eval` to produce a constant integer or Boolean result, so we
restrict its type to require that it produce one.

You should wonder whether we can do the same thing for the *input* to `eval`: if
we could somehow restrict our input to only expressions that have types, then
our evaluation function shouldn't need to include the `Maybe` machinery for
invalid expressions.

In fact, we can do this.. although we have to reach further into Haskell's bag
of tricks than we have so far.  We're going to change our definition of the
expression type to *only* include well-typed expressions.  Essentially, we're
going to moved the rules of the `typed` function into the `Expr` type.  Doing so
looks like this:

-------------------------------------------------------------------------------}

data GExpr a where
  GConst  :: a -> GExpr a
  GPlus   :: GExpr Int -> GExpr Int -> GExpr Int
  GTimes  :: GExpr Int -> GExpr Int -> GExpr Int
  GNegate :: GExpr Int -> GExpr Int
  GIf     :: GExpr Bool -> GExpr a -> GExpr a -> GExpr a

deriving instance Show a => Show (GExpr a)  

{-------------------------------------------------------------------------------

This is different from the data type declarations you're used to in a couple of
ways.  First, we fully write out the type of each constructor.  There's nothing
magic about this; we could have written the earlier type similarly:

    data Expr where
      IConst :: Int -> Expr
      Plus   :: Expr -> Expr -> Expr
      Times  :: Expr -> Expr -> Expr
      Negate :: Expr -> Expr -> Expr
      BConst :: Bool -> Expr
      If     :: Expr -> Expr -> Expr -> Expr

It's just more verbose than the way we have been writing it.  The important part
of this definition is the type parameter `a`.  This is used to carry the type of
the expression we're building.  For example, we have now built in that the
arguments to `GPlus` have to be `Int` typed, and that the result is `Int` typed
as well.  Here's an example:      

-------------------------------------------------------------------------------}

ie1, ie2 :: GExpr Int

ie1 = GPlus (GConst 1) (GConst 2)

ie2 = GTimes (GNegate (GPlus (GConst 1) (GConst 2))) (GConst 3)

{-------------------------------------------------------------------------------

Note that if we violate this rule---say, by trying to negate a Boolean---we'll
actually get a error from the Haskell compiler trying to build our program.

-------------------------------------------------------------------------------}

-- Uncomment this line to see the error
-- ie3 = GTimes (GNegate (GConst True)) (GConst 2)

{-------------------------------------------------------------------------------

Your task is to write the big-step evaluation function for this type.  In
essence, the logic is identical to that you had in problems 1 & 2; the key
difference is that, because we have the additional assurance provided by the
input type, we no longer need the `Maybe` or `Value` types to be involved.

As you're writing this function, think for a minute about how the recursive
calls get typed.  For example, if you're implementing the case `GPlus m n`, you
don't just know that `m` and `n` are expressions; you know that they're
expressions of type `Int`.  What does this tell you about the type of `geval m`
and `geval n`?

-------------------------------------------------------------------------------}

geval :: GExpr a -> a
geval (GConst i) = i
geval (GPlus m n) = geval m + geval n
geval (GTimes m n) = geval m * geval n
geval (GNegate m) = negate (geval m)
geval (GIf l m n) = if geval l then geval m else geval n
