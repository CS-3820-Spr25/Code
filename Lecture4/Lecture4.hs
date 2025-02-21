module Lecture4 where

{- 
   This lecture is about implementing a Sudoku solver.
   We first start with a naive implementation that serves as a
   specification for the solver.
   Then we refine this solver by reasoning about the behavior of
   the specification.

   This section follows Chapter 5 of Richard Bird's
   "Thinking Functionally with Haskell".
-}

-- A general matrix is a list of rows
type Matrix a = [Row a]
-- and a row is just a list of elements.
type Row    a = [a]

-- A Sodoku grid is a special case of a matrix.
-- It is a matrix of digits.
type Grid = Matrix Digit

-- To represent digits we simply use characters.
type Digit = Char

-- The digits that a player can use are the characters
-- from 1 to 9.
digits :: [Char]
digits = ['1' .. '9']

-- To represent a blank cell we use the character '0'.
-- It is useful as a tester function that returns
-- true if a digit is the "blank".
blank :: Digit -> Bool
blank = (== '0')

-- Here are three example Sudoku grids to play around
-- with.  The third one is a realistic grid.
testGrid :: Grid
testGrid = [
    ['0', '2', '3', '0', '0', '0', '0', '0', '0'],
    ['0', '0', '0', '0', '0', '0', '0', '0', '0'],
    ['0', '0', '0', '0', '0', '0', '0', '0', '0'],
    ['0', '0', '0', '0', '0', '0', '0', '0', '0'],
    ['0', '0', '0', '0', '0', '0', '0', '0', '0'],
    ['0', '0', '0', '0', '0', '0', '0', '0', '0'],
    ['0', '0', '0', '0', '0', '0', '0', '0', '0'],
    ['0', '0', '0', '0', '0', '0', '0', '0', '0'],
    ['0', '0', '0', '0', '0', '0', '0', '0', '0']]

-- This one is obviously unsolvable.
testGrid2 :: Grid
testGrid2 = [
    ['1', '2', '3', '4', '5', '6', '7', '8', '9'],
    ['1', '2', '3', '4', '5', '6', '7', '8', '9'],
    ['1', '2', '3', '4', '5', '6', '7', '8', '9'],
    ['1', '2', '3', '4', '5', '6', '7', '8', '9'],
    ['1', '2', '3', '4', '5', '6', '7', '8', '9'],
    ['1', '2', '3', '4', '5', '6', '7', '8', '9'],
    ['1', '2', '3', '4', '5', '6', '7', '8', '9'],
    ['1', '2', '3', '4', '5', '6', '7', '8', '9'],
    ['1', '2', '3', '4', '5', '6', '7', '8', '0']]

testGrid3 :: Grid
testGrid3 = [
    ['5', '0', '0', '0', '8', '0', '0', '4', '9'],
    ['0', '0', '0', '5', '0', '0', '0', '3', '0'],
    ['0', '6', '7', '3', '0', '0', '0', '0', '1'],
    ['1', '5', '0', '0', '0', '0', '0', '0', '0'],
    ['0', '0', '0', '2', '0', '8', '0', '0', '0'],
    ['0', '0', '0', '0', '0', '0', '0', '1', '8'],
    ['7', '0', '0', '0', '0', '4', '1', '5', '0'],
    ['0', '3', '0', '0', '0', '2', '0', '0', '0'],
    ['4', '9', '0', '0', '5', '0', '0', '0', '3']]

{-
   The basic idea of our solver is to maintain a list of choices
   for each cell.  To do this, we move from a grid (a Matrix Digit)
   to a matrix of choices (Matrix [Digit]).

   Then in a second step we generate all possible complete grids
   from such a choice matrix.

   In the third step, we throw away all completions that are not
   valid Sudoku solutions.
-}

-- This is a function that takes a grid a generates a list of
-- all the ways to fill the empty cells.
completions :: Grid -> [Grid]
completions = expand . choices

-- To generate the choice matrix, we map over the entire grid
-- and replace the cells by lists of choices.
-- If a cell is blank we can write any digit, if there is already
-- a digit, we can only write this one.
-- Note that we have a nested map: we map a map function over
-- the rows.
choices :: Grid -> Matrix [Digit]
choices g = map (map choice) g
    where   
        choice d
            | blank d = digits
            | otherwise = [d]

-- To expand the choices into grids, we use a helper function
-- that computes the cartesian product.
-- For example, (cartP [[1,2], [3,4]]) is
-- [[1,3], [1,4], [2,3], [2,4]]
-- I.e., cartP lists all the ways to pick an element out of all
-- the lists.
cartP :: [[a]] -> [[a]]
cartP [] = [[]] 
cartP (xs:xss) = [ x:ys | x <- xs, ys <- yss ]
    where yss = cartP xss 

-- Now we can use the cartesian product function to expand
-- the list of choices.  The inner (map cartP) generates a list
-- of possible rows for each row of choices.
expand :: Matrix [Digit] -> [Grid]
expand = cartP . (map cartP)

-- The remaining ingredient is a test that a Grid is a valid
-- Sudoku grid.  A grid is valid if no digit repeats in each
-- row, in each column and in each 3 by 3 box.
valid :: Grid -> Bool
valid g = all nodups (rows g) &&
          all nodups (cols g) &&
          all nodups (boxs g)

-- The test for the absence of duplicates.
nodups :: [Digit] -> Bool
nodups []     = True
nodups (x:xs) = all (/= x) xs && nodups xs 

{-
   Now we have a list of functions that take a grid of an input
   and transform it such that the thing we are looking at becomes
   the rows.  
-}

-- Rows are already rows, so there is nothing to do here.
-- id is the identity function.
rows :: Matrix a -> Matrix a
rows = id

-- To make rows out of columns, we need to transpose the matrix.
cols :: Matrix a -> Matrix a
cols [xs]     = [ [x] | x <- xs ] 
cols (xs:xss) = zipWith (:) xs (cols xss)

main = return ()

