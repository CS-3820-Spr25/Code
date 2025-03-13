module Tests where

import Control.Monad (join)
import Data.List (partition)
import Data.Maybe 
import System.Exit ( exitWith, ExitCode(ExitFailure, ExitSuccess) )
import System.Environment ( getArgs )
import Test.HUnit
import Text.Read (readMaybe)

import Problems6

--------------------------------------------------------------------------------
-- The actual tests
--------------------------------------------------------------------------------

test1 :: Test
test1 = TestLabel "Exercise 1: Eq instance for BinaryTree" $ TestList
    [ TestCase $ assertEqual "Empty trees are equal"
        (Empty :: BinaryTree Int)
        (Empty :: BinaryTree Int)
    , TestCase $ let tree1 = Node 1 (Node 2 Empty Empty) (Node 3 Empty Empty)
                     tree2 = Node 1 (Node 2 Empty Empty) (Node 3 Empty Empty)
                 in assertEqual "Identical trees are equal" tree1 tree2
    , TestCase $ let tree1 = Node 1 Empty Empty
                     tree2 = Node 2 Empty Empty
                 in assertBool "Different trees are not equal" (tree1 /= tree2)
    ]

test2 :: Test
test2 = TestLabel "Exercise 2: Monoid instance for Expr" $ TestList
    [ TestCase $ assertEqual "mempty is Const 0" mempty (Const 0)
    , TestCase $ let expr1 = Const 1
                     expr2 = Const 2
                     expected = Const 3
                 in assertEqual "mappend combines constants"
                    (expr1 <> expr2) expected
    , TestCase $ let expr1 = Const 1
                     expr2 = Const 2
                     expr3 = Const 3
                 in assertEqual "Monoid associativity law holds"
                    ((expr1 <> expr2) <> expr3) (expr1 <> (expr2 <> expr3))
    , TestCase $ let expr1 = Add [(Const 1), (Const 1)]
                     expr2 = Add [(Const 2), (Const 2)]
                     expr3 = Add [(Const 3), (Const 3)]
                 in assertEqual "Monoid associativity law holds"
                    ((expr1 <> expr2) <> expr3) (expr1 <> (expr2 <> expr3))
    , TestCase $ let expr = Const 1
                 in do
                    assertEqual "Monoid left identity law holds" (mempty <> expr) expr
                    assertEqual "Monoid right identity law holds" (expr <> mempty) expr
    , TestCase $ let expr = Add [(Const 1), (Const 2)]
                 in do
                    assertEqual "Monoid left identity law holds" (mempty <> expr) expr
                    assertEqual "Monoid right identity law holds" (expr <> mempty) expr
    ]

test3 :: Test
test3 = TestLabel "Exercise 3: Functor instance for Box" $ TestList
    [ TestCase $ assertEqual "fmap applies function inside Box"
        (fmap (+1) (Box 1)) (Box 2)
    , TestCase $ assertEqual "fmap preserves identity"
        (fmap id (Box 1)) (Box 1)
    , TestCase $ let f = (+1)
                     g = (*2)
                 in assertEqual "fmap composition law holds"
                    (fmap (f . g) (Box 3)) ((fmap f . fmap g) (Box 3))
    ]

test4 :: Test
test4 = TestLabel "Exercise 4: combineAndMap function" $ TestList
    [ TestCase $ assertEqual "Combines and maps correctly"
        (combineAndMap (+1) [[1,2], [3,4]]) [2,3,4,5]
    , TestCase $ assertEqual "Works with empty list of lists"
        (combineAndMap (+1) []) []
    , TestCase $ assertEqual "Works with empty sublists"
        (combineAndMap (+1) [[], [1,2], []]) [2,3]
    ]

test5 :: Test
test5 = TestLabel "Exercise 5: Ord instance for BinaryTree" $ TestList
    [ TestCase $ let tree1 = Node 2 (Node 1 Empty Empty) (Node 3 Empty Empty)
                     tree2 = Node 2 (Node 1 Empty Empty) (Node 4 Empty Empty)
                 in assertBool "Compares trees based on in-order traversal" (tree1 < tree2)
    , TestCase $ let tree = Node 2 (Node 1 Empty Empty) (Node 3 Empty Empty)
                 in assertEqual "Equal trees are equal under Ord" (compare tree tree) EQ
    , TestCase $ let tree1 = Node 1 Empty Empty
                     tree2 = Node 2 Empty Empty
                 in assertBool "Tree with smaller in-order traversal is less" (tree1 < tree2)
    , TestCase $ let tree1 = Node 1 (Node 0 Empty Empty) Empty
                     tree2 = Node 1 Empty (Node 2 Empty Empty)
                 in assertBool "Tree ordering respects structure and values" (tree1 < tree2)
    ]

--------------------------------------------------------------------------------
-- main
--------------------------------------------------------------------------------

allTests :: [(Int, Test)]
allTests = zip [1..] [test1, test2, test3, test4, test5]

main :: IO ()
main = do
  allArgs <- getArgs
  let (makeJson, testIdxs) = partition ("json" ==) allArgs
      tests | null testIdxs = allTests
            | otherwise = pickTests (ranges testIdxs)
  
  if not (null makeJson) 
  then putStrLn (testsJson tests)
  else do results <- runTestTT (test $ map snd tests)
          if (errors results + failures results == 0)
            then
              exitWith ExitSuccess
            else
              exitWith (ExitFailure 1)

  where ranges [] = []
        ranges (s : ss)
            | Just i <- readMaybe s          = i : ranges ss
            | otherwise                      = error "Unknown ranges"
      
        pickTests (i : j : ks) = between i j ++ pickTests ks
        pickTests [i]          = [allTests !! (i - 1)]
        pickTests []           = []
      
        between i j = take (j - i + 1) (drop (i - 1) allTests)

        testsJson tests =
            unlines [ "{\"name\" : \"Problem " ++ show n ++ "\", \"setup\" : \"\", \"run\" : \"cabal run Tests " ++ show n ++ "\", \"input\" : \"\", \"output\" : \"\", \"comparison\" : \"included\", \"timeout\" : 0.5, \"points\" : 1 },"
                    | (n, _) <- tests
                    ]
