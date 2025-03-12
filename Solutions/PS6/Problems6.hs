module Problems6 where

{-------------------------------------------------------------------------------

CS:3820 Spring 2024 Problem Set 6
=================================

This problem set includes exercises related to type classes in Haskell.

-------------------------------------------------------------------------------}

-- [Exercise 1] Implementing Eq for a Custom Binary Tree
{-

See the binary tree datatyp defined below.

Make it an instance of the `Eq` type class so that two trees are considered
equal if they have the same structure and the stored elements are equal.

-}

data BinaryTree a = Empty | Node a (BinaryTree a) (BinaryTree a)
                  deriving (Show)

-- Implement the Eq instance for BinaryTree
instance Eq a => Eq (BinaryTree a) where
  -- (==) :: Eq a => BinaryTree a -> BinaryTree a -> Bool
  Empty == Empty               = True
  Node x l1 r1 == Node y l2 r2 = x == y && l1 == l2 && r1 == r2
  _ == _                       = False



{-------------------------------------------------------------------------------

[Exercise 2] Implementing Monoid for a Custom Data Type
-------------------------------------------------------

Consider the following data type that represents a simple mathematical expression:

-}

data Expr = Const Int
          | Add [Expr]
          deriving (Show, Eq)

{-

Implement the `Monoid` type class for `Expr` such that `mempty` represents
a zero constant, and the binary operation `mappend` (or `<>`) combines
two expressions.  You will have to make a distinction between constants
and additions.

Recall the monoid laws:

x <> mempty = x
mempty <> x = x
(x <> y) <> z = x <> (y <> z)

-}

-- Implement the Semigroup instance for Expr
instance Semigroup Expr where
    -- (<>) :: Expr -> Expr -> Expr
    (<>) (Const 0) x = x
    (<>) x (Const 0) = x
    (<>) (Const a) (Const b) = Const (a + b)
    (<>) (Add xs) (Add ys) = Add (xs ++ ys)


-- Implement the Monoid instance for Expr
instance Monoid Expr where
    -- mempty :: Expr
    mempty = Const 0

{-------------------------------------------------------------------------------

[Exercise 3] Implementing Functor for a Custom Data Type
--------------------------------------------------------

The Box datatype defined below is a very simple data type: it stores a single
value.

Implement the `Functor` type class for `Box`.

-}

data Box a = Box a
  deriving (Show, Eq)

-- Implement the Functor instance for Box
instance Functor Box where
    -- fmap :: (a -> b) -> Box a -> Box b
    fmap f (Box x) = Box (f x)

{-------------------------------------------------------------------------------

[Exercise 4] Using an Existing Instance to Implement Another
------------------------------------------------------------

Recall that List datatypes are instances of both the `Functor` and `Monoid`,
typeclass.

Define a function `combineAndMap` that takes a list of lists, concatenates
them into a single list (using the monoid operation), and then applies
a function to each element (using the functor operation).

-}

combineAndMap :: (a -> b) -> [[a]] -> [b]
combineAndMap f xs = fmap f (mconcat xs)


{-------------------------------------------------------------------------------

[Exercise 5] Implementing Ord Based on an Existing Eq Instance
--------------------------------------------------------------

Implement the `Ord` type class for the `BinaryTree` data type from Exercise 1.

A tree `A` is considered to be less than another tree `B`, if the element in
the root of `A` is less than the element in the root of `B`.  If the
root elements are the same, then `A` is less than `B` if the left subtree
of `A` is less than the left subtree of `B`.  If the left subtrees are the
same, then the right subtrees are compared in the same manner.

A leaf (`Empty`) is always smaller than a `Node`.

-}

-- Implement the Ord instance for BinaryTree
instance (Ord a) => Ord (BinaryTree a) where
    -- compare :: Ord a => BinaryTree a -> BinaryTree a -> Ordering
    compare Empty Empty = EQ
    compare Empty _     = LT
    compare _     Empty = GT
    compare (Node x l1 r1) (Node y l2 r2)
      | x < y = LT
      | x > y = GT
      | l1 == l2 = compare r1 r2
      | otherwise = compare r1 r2
