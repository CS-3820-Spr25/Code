{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" "Use concatMap" #-}
module Problems4 (module Problems4) where

import Data.List (isPrefixOf)

{-------------------------------------------------------------------------------

CS:3820 Spring 2025 Problem Set 4
=================================

This problem set explores the definition and use of several tree-like container
types in Haskell.  This combines our experience with structuring data from
Problem Set 2 with our experience with recursion from Problem Set 3.

-------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------

Problems 1-3: Binary trees
--------------------------

Our first data structure is a binary tree---that is, a tree at which each branch
has two children.  We can express this directly in Haskell:

-------------------------------------------------------------------------------}

data BinTree a = LeafB | BranchB a (BinTree a) (BinTree a)
  deriving Show

{-------------------------------------------------------------------------------

That is: a binary tree of `a`s is either a leaf (which carries no value), or a
branch, which carries a values of type `a` and left and right subtrees of type
`BinTree a`.  For examples, here's a simple binary tree containing four values:

-------------------------------------------------------------------------------}

bt1 :: BinTree Int
bt1 = BranchB 4 (BranchB 1 LeafB (BranchB 2 LeafB LeafB)) (BranchB 5 LeafB LeafB)

{-------------------------------------------------------------------------------

Drawing this tree, it would look something like:

        4
      /   \
    1       5
   / \     / \
  .   2   .   .
     / \
    .   .

where I've labeled the branches, and written `.` for the leaves.

-------------------------------------------------------------------------------}

--------------------------------------------------------------------------------
-- Problem 1: sumBT
--
-- Your first task is to write a function that sums the values in a binary tree.
-- The empty binary tree should have sum 0.  For example,e the tree above would
-- have sum 12.

sumBT :: BinTree Int -> Int
sumBT LeafB = 0
sumBT (BranchB x l r) = x + sumBT l + sumBT r

--------------------------------------------------------------------------------
-- Problem 2: insertBT
--
-- One common application of binary trees is as *search* trees.  In this
-- interpretation, we assume that our binary trees have an additional property:
-- that at a branch
--
--       x
--      / \
--     l   r
--
-- the values in tree `'l` are all less than `x`, and the values in `r` are all
-- greater than `x`.  Our tree above maintains this invariant; on the other
-- hand, a tree like
--
--        0
--      /   \  
--     1     .
--    / \
--   .   .
--
-- does not, because 1 is not less than 0.
--
-- For this task, you are given a new integer and a tree; you should *assume*
-- that tree already obeys the binary search tree invariant.  You should return
-- a binary search tree that contains both the new value and the value already
-- in the tree, by transforming one of the tree's leaves to a branch.  For
-- example, given the tree
--
--        1
--      /   \
--     0     2
--    / \   / \
--   .   . .   .
--
-- inserting the value `3` should result in
--
--        1
--      /   \
--     0     2
--    / \   / \
--   .   . .   3
--            / \
--           .   .
--
-- If the value to insert is *already* in the tree, you should return a tree
-- identical to the original tree.
  
insertBT :: Int -> BinTree Int -> BinTree Int 
insertBT x LeafB = BranchB x LeafB LeafB
insertBT x (BranchB y l r)
  | x < y  = BranchB y (insertBT x l) r
  | x == y = BranchB y l r
  | x > y  = BranchB y l (insertBT x r)

--------------------------------------------------------------------------------
-- Problem 3: mapBT
--
-- Your third task is to implement a mapping function for binary trees.  Given a
-- function `f` and a tree like
--
--        x
--      /   \
--     y     z
--    / \   / \
--   .   . .   w
--            / \
--           .   .
--
-- (where it doesn't really matter that the x...w are), your function should return a tree like
--
--       f x
--      /   \
--    f y    f z
--    / \   / \
--   .   . .  f w
--            / \
--           .   .
--
-- Note that your function doesn't have to do anything to leaves; the function
-- only transforms (the values stored at) branches.

mapBT :: (a -> b) -> BinTree a -> BinTree b
mapBT _ LeafB = LeafB
mapBT f (BranchB x l r) = BranchB (f x) (mapBT f l) (mapBT f r)

{-------------------------------------------------------------------------------

Problems 4-5: Rose trees
------------------------

Binary trees have a fixed form: each branch has exactly two children.  Rose
trees are the generalization of this idea: we allow each branch to have
arbitrarily many children, and indeed for different branches in the same tree to
have different numbers of branches.  We can capture this in Haskell by:

-------------------------------------------------------------------------------}

data RoseTree a = BranchR a [RoseTree a]
  deriving Show

{-------------------------------------------------------------------------------

We don't have a separate constructor for leaves; instead, we can represent a
leaf as a branch with no children.  This does mean, in contrast to the previous
version, that leaves do carry tags.  Here is an example rose tree:

-------------------------------------------------------------------------------}

rt1 :: RoseTree Int
rt1 = BranchR 1 [BranchR 2 [BranchR 3 [], 
                            BranchR 4 [BranchR 5 [], BranchR 6 []], 
                            BranchR 7 [BranchR 8 [], BranchR 9 [], BranchR 10 []]]]

{-------------------------------------------------------------------------------

Drawing this tree would look something like this:

                           1
                           |
                           2
                     ,-----+------,
                    /      |       \
                   3       4        7
                          / \     / | \
                         5   6   8  9  10

-------------------------------------------------------------------------------}

--------------------------------------------------------------------------------
-- Problem 4: sumRT
--
-- First, you should implement a function that sums all the values in a rose
-- tree.  For example, the sum of the tree above is 1 + ... + 10 = 55.
--
-- When implementing recursive functions over rose trees, you have *two* levels
-- of recursion: `RoseTree`s contain *lists* of `RoseTree`s, so your code will
-- include a layer of recursion for the lists and another layer of recursion for
-- your `RoseTree`s.  You may even find it helpful to write a separate function
-- `sumRTs :: [RoseTree Int] -> Int` to handle the inner recursion.

sumRT :: RoseTree Int -> Int
sumRT (BranchR x ts) = x + sum (map sumRT ts) 

--------------------------------------------------------------------------------
-- Problem 5: flattenRT
--
-- Next, you should implement a function that extracts all the values from a
-- rose tree.  There are a couple of orders in which you could do this.  For our
-- purposes, we want to proceed *depth*-first.  In the example above, we would
-- produce:
--
--    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
--
-- You should *not* produce
--
--    [1, 2, 3, 4, 7, 5, 6, 8, 9, 10]
-- 
-- ...which would be the result of a *breadth*-first traversal.
--
-- Again, you may want to write a helper function `flattenRTs :: [RoseTree a] ->
-- a`.  In writing your functions, you may find the function `concat :: [[a]] ->
-- [a]` helpful. `concat` concatenates all the lists in its argument; for
-- example, `concat [[1, 2], [3, 4]]` produces `[1, 2, 3, 4]`.

flattenRT :: RoseTree a -> [a]
flattenRT (BranchR x ts) = x : concat (map flattenRT ts)

{-------------------------------------------------------------------------------

Problems 6-8
------------

A variation of a rose trie is a "trie", or prefix tree.  A trie represents a set
of strings (or other sequences of values); each branch is indexed not be a
single value, but by a sequence of values.

-------------------------------------------------------------------------------}

data Trie = BranchT Bool [(String, Trie)]
  deriving Show

{-------------------------------------------------------------------------------

Here is an example trie:

-------------------------------------------------------------------------------}

tr1 :: Trie
tr1 = BranchT False [("h", BranchT False 
                                   [ ("awk", BranchT True [("eye", BranchT True [("s",BranchT True [])])])
                                   ,("eli", BranchT False [ ("copter", BranchT True [])
                                                          , ("os",BranchT True [])])])]

{-------------------------------------------------------------------------------

This trie represents the strings

  hawk, hawkeye, hawkeyes, helicoper, helios

To see how "hawkeye" is captured in this tree, we follow from the root. At the
root, we have a branch labeled "h", which is part of the string for which we are
looking.  Next, we look in the children of that node; we find a branch labeled
"awk", which is also part of our string, so we continue.  Next, we find a branch
labeled "eye", so we follow that branch.  Finally, we have run out of our source
string, so we check to see if that branch is included; the Boolean True
indicates that it is.

On the other hand "heli" is not included in the set.  To see this, we again
start from the root.  We find the "h" branch, and then the "eli" branch.  We
have run out of our search string, so we check to see if this branch is
included.  The Boolean False indicates that it is not.

Finally, "pickle" is also not included.  To see this, we start out by looking
for any branch in common with "pickle"; the only branch is "h", which is not the
beginning of "pickle", so the string is not included.

-------------------------------------------------------------------------------}

--------------------------------------------------------------------------------
-- Problem 6: memberT
--
-- Your first task is to implement the process above, determining whether or not
-- a string is included in a trie.  As in the problems above, you have two
-- levels of recursion here: one on `Trie`s, and one on `[(String, Trie)]`
-- lists.  You might find it helpful to define a helper function
--
--      memberTs :: String -> [(String, Trie)] -> Bool
--
-- You may find some functions from the standard libraries helpful:
--
--    isPrefixOf :: [a] -> [a] -> Bool     -- returns True if the first list is 
--                                         -- a prefix of the second
--
--    length :: [a] -> Int        -- returns the length of a string
--
--    drop :: Int -> [a] -> [a]   -- `drop n xs` returns `xs` without the first
--                                -- `n` elements.

memberT :: String -> Trie -> Bool
memberT [] (BranchT b _) = b
memberT cs (BranchT _ ts) = any memberB ts
  where memberB (ds, t) = ds `isPrefixOf` cs && memberT (drop (length ds) cs) t

--------------------------------------------------------------------------------
-- Problem 7: commonPrefix
--
-- For this problem, you'll write a helper function that will be useful in the
-- next problem.  The `commonPrefix` function takes two strings and returns the
-- longest string that is a prefix of both strings.  Here are some examples
--
--     commonPrefix "hello" "helicopter"   --> "hel"
--     commonPrefix "heli" "helicopter"    --> "heli"
--     commonPrefix "hello" "pickle"       --> ""

commonPrefix :: String -> String -> String
commonPrefix [] _ = []
commonPrefix _ [] = []
commonPrefix (c : cs) (d : ds) 
  | c == d    = c : commonPrefix cs ds
  | otherwise = []

--------------------------------------------------------------------------------
-- Problem 8: insertT
--
-- Finally, you should write a function that inserts a string into a trie.  In
-- terms of the earlier example, you should have:
--
--     memberT "pickle" tr1                       --> False
--     memberT "pickle" (insert "pickle" tr1)     --> True
--
-- I *strongly* recommend breaking your logic into two functions: 
--
--    insertT :: String -> Trie -> Trie
--    insertTs :: String -> [(String, Trie)] -> [(String, Trie)]
--
-- Of course, these functions will need to call each other.
--
-- When comparing the string to be inserted to a branch label in `insertTs`, you
-- may want to consider the following cases:
--
--  * No prefix in common
--  * The branch label is a prefix of the inserted string
--  * The inserted string is equal to the branch label
--  * The inserted string is a prefix of the branch label
--  * The inserted string and the branch label have a common prefix.
--
-- Each of these cases will lead to a *different* behavior of `insertTs`.    

insertT :: String -> Trie -> Trie
insertT [] (BranchT _ ts) = BranchT True ts
insertT cs (BranchT b ts) = BranchT b (insertB ts)
  where insertB [] = [(cs, BranchT True [])]
        insertB ((ds, t@(BranchT b' ts')) : bs) 
          | null es = (ds, t) : insertB bs
          | cs == ds = (ds, BranchT True ts') : bs
          | cs == es = (es, BranchT True [(drop (length es) ds, t)]) : bs
          | ds == es = (es, insertT (drop (length es) cs) t) : bs
          | otherwise = (es, BranchT False [(drop (length es) cs, BranchT True []), (drop (length es) ds, t)]) : bs
          where es = commonPrefix cs ds

t1, t2, t3 :: Trie

t1 = BranchT False [("p", BranchT False [("lant", BranchT True []), ("aper", BranchT True [])])]

t2 = BranchT False [("p", BranchT False [("lant", BranchT True []), ("aper", BranchT True [])]), ("umbrella", BranchT True [])]

t3 = BranchT False [("t", BranchT False [("est", BranchT True [("er", BranchT True [])]), ("oast", BranchT True [])])]
