module Tests where

import Data.List (partition)
import System.Exit ( exitWith, ExitCode(ExitFailure, ExitSuccess) )
import System.Environment ( getArgs )
import Test.HUnit
import Text.Read (readMaybe)

import Problems3


--------------------------------------------------------------------------------
-- Tests 1

tests1, tests2, tests3, tests4, tests5, tests6, tests7, tests8 :: Test

tests1 = test $
  -- simple tests
  [ semifact 0 ~?= 1
  , semifact 1 ~?= 1
  , semifact 2 ~?= 2
  , semifact 3 ~?= 3
  , semifact 4 ~?= 8
  ]
  ++
-- Some facts about !!, ∀ n ∈ N:
--    n!! ≡ (n - 2)!! mod n
  [semifact n `mod` semifact (n - 2) ~?= 0 | n <- [1..15]]
  ++
--     n!!
--   –—————— = n
--  (n - 2)!!
  [semifact n `div` (semifact (n - 2)) ~?= n | n <- [1..10]]
  ++
--  n!! * (n - 1)!! = n!
  [semifact 7 * semifact 6 ~?= 7 * 6 * 5 * 4 * 3 * 2]


--------------------------------------------------------------------------------
-- Tests 2

tests2 = test $
  [ last (collatz x) ~?= 1 | x <- [15..20]] ++
  [ head (collatz x) ~?= x | x <- [35..40]] ++
  [ take 5 (collatz 50) ~?= [50, 25, 76, 38, 19]]

--------------------------------------------------------------------------------
-- Tests 3

tests3 = test $
  [ endsInOne (collatz x) ~?= True | x <- [15..20]] ++
  [ endsInOne [x] ~?= False | x <- [35, 37, 39, 41]] ++
  [ endsInOne [] ~?=  False] ++
  [ endsInOne [1] ~?=  True]

--------------------------------------------------------------------------------
-- Tests 4

tests4 = test
  [ evenIndexes "Curabitur lacinia pulvinar nibh" ~?= "uaiu aii uvnrnb"
  , evenIndexes n                                 ~?= n
  , evenIndexes [()]                              ~?= []
  , evenIndexes [1..100]                          ~?= [2,4..100]]
  where
  n :: [Bool]
  n = []

--------------------------------------------------------------------------------
-- Tests 5

tests5 = test
  [ alternating []                ~?= 0
  , alternating [1337]            ~?= -1337
  , alternating [100, 50, 25, 12] ~?= -100 + 50 - 25 + 12
  , alternating [1..100]          ~?= 50
  , alternating [(-25)..(-1)]     ~?= 13]

--------------------------------------------------------------------------------
-- Tests 6

tests6 = test
  [ subsetsum [1, 2, 3] 5         ~?= True
  , subsetsum [1 ,2, 5] 4         ~?= False
  , subsetsum [] 0                ~?= True
  , subsetsum [] 1                ~?= False
  , subsetsum [3, 2, 3, 2] 6      ~?= True
  , subsetsum [3, 2, 9, 2] 6      ~?= False
  , subsetsum [1, 4, 3] 5         ~?= True]

--------------------------------------------------------------------------------
-- Tests 7

tests7 = test
  [ subsetsumResult [1, 2, 3] 5         ~?= Just [False, True, True]
  , subsetsumResult [1 ,2, 5] 4         ~?= Nothing
  , subsetsumResult [] 0                ~?= Just []
  , subsetsumResult [] 1                ~?= Nothing
  , subsetsumResult [3, 2, 3, 2] 6      ~?= Just [True, False, True, False]
  , subsetsumResult [3, 2, 9, 2] 6      ~?= Nothing
  , subsetsumResult [1, 4, 3] 5         ~?= Just [True, True, False]]

--------------------------------------------------------------------------------
-- Tests 8

tests8 = test
  [ mapNeighbors myLambda 0 [1, 2, 3] ~?= [(1, 1), (2, 1), (3, -3)]
  , mapNeighbors myLambda 1 [1, 2, 3] ~?= [(1, 1), (2, 1), (3, -2)]]

--------------------------------------------------------------------------------
-- main
--------------------------------------------------------------------------------

allTests :: [(Int, Test)]
allTests = zip [1..] [tests1, tests2, tests3, tests4, tests5, tests6, tests7, tests8]

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
            where go []           = []
                  go (i : j : ks) = i : j : go ks
      
        pickTests (i : j : ks) = between i j ++ pickTests ks
        pickTests [i]          = [allTests !! (i - 1)]
        pickTests []           = []
      
        between i j = take (j - i + 1) (drop (i - 1) allTests)

        testsJson tests =
            unlines [ "{\"name\" : \"Problem " ++ show n ++ "\", \"setup\" : \"\", \"run\" : \"cabal run Test " ++ show n ++ "\", \"input\" : \"\", \"output\" : \"\", \"comparison\" : \"included\", \"timeout\" : 0.5, \"points\" : 1 },"
                    | (n, t) <- tests
                    ]
