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

-- The most involved function is the boxs function.  We need
-- to make a row out of each box.  This works by putting three
-- successive elements together and then transposing the
-- result using the cols function.
-- See the illustration on page 95 of Bird's book.
group :: [a] -> [[a]]
group [] = []
group xs = (take 3 xs):(group (drop 3 xs))

ungroup :: [[a]] -> [a] 
ungroup = concat

boxs :: Matrix a -> Matrix a
boxs = map ungroup . ungroup .
       map cols .
       group . map group

{-
    Here is an example calculation:

    We want to show that: "boxs . boxs = id"

    And we know:
    ungroup . group = id
    group . ungroup = id

    boxs . boxs is:
    map ungroup . ungroup . map cols . group . map group . 
    map ungroup . ungroup . map cols . group . map group 

    by map law:
    map ungroup . ungroup . map cols . group .
    map (group . ungroup) .
    ungroup . map cols . group . map group 

    by group inverse:
    map ungroup . ungroup . map cols . group .
    map id .
    ungroup . map cols . group . map group 

    by map law, and composition with identity:
    map ungroup . ungroup . map cols . group .
    ungroup . map cols . group . map group 

    by group inverse
    map ungroup . ungroup . map cols . map cols . group . map group 

    by map law
    map ungroup . ungroup . map (cols . cols) . group . map group 

    by col is involution 
    map ungroup . ungroup . group . map group 

    by group inverse 
    map ungroup . map group 

    by map law
    map (ungroup . group) 

    by group inverse and map law  
    id
-}

{- 
At this point we have all the ingredients for the solve function.
However, we want to improve our solver to be efficient.

The idea is to remove choice from the choice lists before expanding.
This is similar to how a human reasons: if there is already a 3 in
a row, then 3 is not an option for any in the cells in that row.

Hence our solve function will be:
-}
-- solve = filter valid . expand . prune . choices

-- This function implements the idea described above.  The
-- fixed helper lists all digits where there are no other choices.
pruneRow :: Row [Digit] -> Row [Digit]
pruneRow row = map (remove fixed) row
    where fixed = [ d | [d] <- row ]

-- This is a function that removes a list of digits from
-- another list.
remove :: [Digit] -> [Digit] -> [Digit]
remove ds [x] = [x]
remove ds xs  = filter (`notElem` ds) xs

-- We can also apply the same idea to columns and boxes.
-- As we saw above, we can use cols and boxs to see the
-- columns and boxes as "rows".

{-
This works, because the functions we are using have some universal
properties.
For example, the conversion functions are involutions:

rows. rows = id
cols . cols = id
boxs . boxs = id

Furthermore, there is the map law:

map (f . g) = map f . map g

Putting these identities together justifies simplifications
like the one below.  See section 5.2 of Bird's book.

-}

{-
Properties we know:

This is the key property: pruneRow is such that we can add it
before we expand the choices with `cartp`.
filter nodups . cartp = filter nodups . cartp. pruneRow

Where can we add this into the solver to get a more efficient solver?
To do this we expand `solve` until we find the subterm
`filter nodups . cartp` that we can replace with `filter nodups . cartp pruneRow`

We also know that if  f . f = id then
a) filter (p . f) = map f . filter p . map f
b) filter (p . f) . map f  = map f . filter p
c) filter (all p) . cartp = cartp . map (filter p)

Our solver is:
filter valid . expand =
    filter (all nodups . rows ) .
    filter (all nodups . cols ) .
    filter (all nodups . boxs ) . expand

Let's look at:
filter (all nodups . boxs ) . expand = (by property a)
map boxs . filter (all nodups) . map boxs . expand =
map boxs . filter (all nodups) . expand . boxs     = (definition of expand)
map boxs . filter (all nodups) . cartp . (map cartp) . boxs     = (by property c)
map boxs . cartp . map (filter nodups) . (map cartp) . boxs     = (by map laws)
map boxs . cartp . map (filter nodups . cartp) . boxs

by pruning:
map boxs . cartp . map (filter nodups . cartp . pruneRow) . boxs = (by map laws)
map boxs . cartp . map (filter nodups) . map (cartp . pruneRow) . boxs = (reverse of property c)
map boxs . cartp . filter (all nodups) . cartp . map (cartp . pruneRow) . boxs = (by map laws)
map boxs . cartp . filter (all nodups) . cartp . map cartp . map pruneRow . boxs = (by def. of expand)
map boxs . cartp . filter (all nodups) . expand . map pruneRow . boxs = (by prop. b)
filter (all nodups . boxs) . map boxs . expand . map pruneRow . boxs =
filter (all nodups . boxs) . expand . boxs  . map pruneRow . boxs

Let's add a helper: pruneBy f = f . map pruneRow . f
-}


-- This gives us a general function that can be parameterized.
pruneBy f = f . map pruneRow . f

-- and of course we want to use all three pruning directions.
prune :: Matrix [Digit] -> Matrix [Digit]
prune = pruneBy boxs . pruneBy cols . pruneBy rows

-- we can do even more: since pruning might reduce the choices
-- in a cell to only one digit, it might unlock more prunes.
-- This function applies any function until the result doesn't
-- change anymore (a fixed point is reached). 
many :: (Eq a) => (a -> a) -> a -> a
many f x = if x == y then x else many f y
    where y = f x

-- Putting everything together gives us
solve :: Grid -> [Grid]
solve = filter valid . expand . (many prune) . choices

{- We can do even better: instead of pruning and then generating
   a long list of expanded grids.  We only expand a single cell.
   This means we split a matrix of choices into multiple matrices
   of choices, and continue pruning on these individually.

   To implement this, we need to change our notions of valid and expand.
-}

-- This is a helper that tests whether there are no choices left in a cell.
single :: [a] -> Bool
single [_] = True
single _ = False

{- This function expands any one cell, namely the first one that has more than
   one choice left (where single is false).  It uses the builtin break function
   that breaks a list into two at the first element where a function evaluates
   to true -}
expand1 :: Matrix [Digit] -> [Matrix [Digit]]
expand1 rows =
   [rows1 ++ [ row1 ++ [c]:row2 ] ++ rows2 | c <- cs]
   where
    (rows1, row:rows2) = break (any (not . single)) rows
    (row1, cs:row2)    = break (not . single)       row

-- This function returns true if there a now choices left.
complete :: Matrix [Digit] -> Bool
complete = all (all single)

-- This function takes a complete matrix and translates it into
-- a grid by simply getting the head element of the (unit)
-- choice lists.
extract :: Matrix [Digit] -> Grid
extract = map (map head)

-- This is a weaker version of valid, it returns false if
-- any "fixed cells" (cells with only one choice left) are
-- contradicting each other.
safe :: Matrix [Digit] -> Bool
safe g = all ok (rows g) &&
         all ok (cols g) &&
         all ok (boxs g)
         where ok row = nodups [x | [x] <- row]

-- Now we can put everything together.  The search function
-- is a thin wrapper around the earlier functions that
-- uses expand1 with prune.  The grid is done once we have
-- a complete and safe grid.
solve' :: Grid -> [Grid]
solve' = search . choices
  where search cm
          | not (safe pm) = []
          | complete pm = [extract pm]
          | otherwise = concat (map search (expand1 pm))
             where pm = prune cm

main = return ()

