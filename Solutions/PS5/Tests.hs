module Tests where

import Data.List (partition, tails, (\\), intersect)
import System.Exit ( exitWith, ExitCode(ExitFailure, ExitSuccess) )
import System.Environment ( getArgs )
import Test.HUnit
import Text.Read (readMaybe)
import Control.Monad
import Control.Monad.State
import Control.Monad.Except

import Problems5

--------------------------------------------------------------------------------

test1, test2, test3 :: Test

test1 = test [ length listOfRooms ~?= 11
             , elem Empty listOfRooms ~?= True
             , elem (Monster 1 2) listOfRooms ~?= True
             , elem (ArrowShop 2) listOfRooms ~?= True]

test2 = test [ length listOfLocals ~?= 44
             , elem (Desert, Empty) listOfLocals ~?= True
             , elem (Desert, Monster 1 2) listOfLocals ~?= True
             , elem (Desert, ArrowShop 2) listOfLocals ~?= True
             , elem (Forest, Empty) listOfLocals ~?= True
             , elem (Forest, Monster 1 2) listOfLocals ~?= True
             , elem (Forest, ArrowShop 2) listOfLocals ~?= True]

test3 = test [ allMaps 1 ~?= map (: []) listOfLocals
             , length (allMaps 2) ~?= 1936
             , length (allMaps 3) ~?= 85184
             , elem [(Swamp,Monster 2 2),(Desert,Empty)] (allMaps 2) ~?= True]

--------------------------------------------------------------------------------

test4, test5, test6 :: Test

test4 = test [ biomeRepeats [] ~?= False
             , biomeRepeats [(Swamp,Monster 2 2),(Desert,Empty)] ~?= False
             , biomeRepeats [(Swamp,Monster 2 2),(Swamp,Empty)] ~?= True
             , biomeRepeats [(Desert, Monster 1 2), (Desert, Monster 1 2)] ~?= True
             , biomeRepeats [(Forest, ArrowShop 2), (Forest, ArrowShop 2)] ~?= True
             , biomeRepeats [(Forest, ArrowShop 2), (Forest, ArrowShop 1)] ~?= True
             , biomeRepeats [(Plains, Empty), (Plains, ArrowShop 2)] ~?= True
             , biomeRepeats [(Plains, Empty), (Plains, Empty)] ~?= True
             , biomeRepeats [(Desert, Treasure 4), (Desert, Treasure 3)] ~?= True
             , biomeRepeats [(Desert, Treasure 3), (Desert, Treasure 3)] ~?= True
             , biomeRepeats [(Swamp, Empty), (Swamp, Monster 2 2)] ~?= True
             , biomeRepeats [(Plains, Treasure 3), (Swamp, Treasure 4)] ~?= False
             , biomeRepeats [(Plains, Treasure 2), (Swamp, Treasure 4)] ~?= False
             , biomeRepeats [(Plains, Treasure 1), (Swamp, Treasure 4)] ~?= False
             , biomeRepeats [(Swamp, Treasure 4), (Swamp, Treasure 4)] ~?= True
             , biomeRepeats [(Forest, Treasure 4), (Swamp, Treasure 4)] ~?= False]

test5 = test [ winnable [] ~?= True
             , winnable [(Swamp,Monster 2 2),(Desert,Empty)] ~?= False
             , winnable [(Swamp,Treasure 2),(Swamp,ArrowShop 1),(Swamp,Monster 2 2)] ~?= True
             , winnable [(Swamp,Treasure 2),(Swamp,ArrowShop 2),(Swamp,Monster 2 2)] ~?= False
             , winnable [(Swamp,Treasure 2),(Swamp,ArrowShop 1),(Swamp,Monster 3 2)] ~?= False
             , winnable [(Swamp,Treasure 3),(Swamp,ArrowShop 2),(Swamp,Monster 1 1),
                          (Swamp,ArrowShop 1),(Swamp,Monster 1 1)                  ] ~?= True
             , winnable [(Swamp,Treasure 1),(Swamp,ArrowShop 1),(Swamp,Monster 2 2)] ~?= False
             , winnable [(Swamp,Treasure 2),(Swamp,ArrowShop 1),(Swamp,Monster 2 2)] ~?= True
             , winnable [(Swamp,Treasure 1),(Swamp,ArrowShop 2),(Swamp,Monster 2 2)] ~?= False
             , winnable [(Swamp,Empty),(Swamp,ArrowShop 1),(Swamp,Monster 2 2)] ~?= False
             , winnable [(Swamp,Treasure 2),(Swamp,Empty),(Swamp,Monster 2 2)] ~?= False
             , winnable [(Swamp,Treasure 2),(Swamp,ArrowShop 1),(Swamp,Empty)] ~?= True
             , winnable [(Swamp,Monster 2 2),(Swamp,ArrowShop 1),(Swamp,Monster 2 2)] ~?= False]

test6 = test [ length (winnableMaps 1) ~?= 0
             , length (winnableMaps 2) ~?= 0
             , length (winnableMaps 3) ~?= 1408
             , elem [(Swamp,Treasure 2),(Swamp,ArrowShop 1),(Swamp,Monster 2 2)] (winnableMaps 3) ~?= True
             , elem [(Swamp,Monster 2 2),(Desert,Empty)] (winnableMaps 2) ~?= False
             , elem [(Swamp,Monster 2 2),(Desert,Empty)] (winnableMaps 3) ~?= False
             , elem [(Swamp,Empty),(Desert,Empty)] (winnableMaps 2) ~?= False
             , elem [(Swamp,Monster 2 2),(Swamp,ArrowShop 1),(Swamp,Monster 2 2)] (winnableMaps 3) ~?= False
             , elem [(Swamp, ArrowShop 1), (Desert, Treasure 4)] (winnableMaps 2) ~?= False]

--------------------------------------------------------------------------------
-- main
--------------------------------------------------------------------------------

allTests :: [(Int, Test)]
allTests = zip [1..] [test1, test2, test3, test4, test5, test6]

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
