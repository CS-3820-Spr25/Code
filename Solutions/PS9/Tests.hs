module Tests where

import Data.List (partition, tails, (\\), intersect)
import System.Exit ( exitWith, ExitCode(ExitFailure, ExitSuccess) )
import System.Environment ( getArgs )
import Test.HUnit
import Text.Read (readMaybe)
import Control.Monad
import Control.Monad.State
import Control.Monad.Except

import Problems9

--------------------------------------------------------------------------------
-- This is an unpleasant hack, but I can't be arsed to minimize DFAs.

matches :: String -> GRegex -> Bool
matches s r = "" `elem` go s r where

  go :: String -> GRegex -> [String]
  go _ None = []
  go cs Empty = [cs]
  go [] (Chars _) = []
  go (c : cs) (Chars []) = []
  go (c : cs) (Chars ds) 
    | c `elem` ds = [cs]
    | otherwise   = []
  go cs (r :/\: s) = go cs r `intersect` go cs s
  go cs (r :\/: s) = go cs r ++ go cs s
  go cs (Not r) = tails cs \\ go cs r
  go cs (r :<>: s) = go cs r >>= flip go s 
  go cs (Star r) = 
    go cs (r :<>: Star r) ++ [cs]

checkRegexEquiv :: GRegex -> GRegex -> [String] -> Test
checkRegexEquiv r1 r2 ss =
    test [assertBool ("Regular expressions (" ++ show r1 ++ ") and (" ++ show r2 ++ ") differ on " ++ show s) (matches s r1 == matches s r2) | s <- ss]

---------------------------------------------------------------------------------

test1, test2, test3 :: Test

test1 = test [ test [ test (assertBool "Regular expression doesn't rely on single characters" (singleCharsOnly r'))
                    , checkRegexEquiv r r' ss ] | r <- rs, let r' = singleChars r]
  where rs = [ None, Empty, Chars [], Chars "a", Chars "abc" ]
        ss = [ "", "a", "b", "c" ]

test2 = test [ test [ test (assertBool "Regular expression doesn't rely on single characters" (singleCharsOnly r'))
                    , checkRegexEquiv r r' ss ] | r <- rs, let r' = singleChars r]
  where rs = [ Chars "abc" :/\: Chars "def", Chars "abc" :\/: Chars "def", Not (Chars "abc")
             , Chars "abc" :/\: (Chars "def" :\/: Chars "ab"), Chars "abc" :\/: (Chars "def" :/\: Chars "ef")
             , Chars "abc" :/\: Not (Chars "de"), Chars "abc" :/\: (Not (Chars "d") :\/: Not (Chars "e"))
             , Chars "abc" :\/: (Not (Chars "ab") :/\: Not (Chars "c")) ]
        ss = [ "", "a", "b", "c", "d", "e", "f" ]

test3 = test [ test [ test (assertBool "Regular expression doesn't rely on single characters" (singleCharsOnly r'))
                    , checkRegexEquiv r r' ss ] | r <- rs, let r' = singleChars r]
  where rs = [ Chars "abc" :<>: Chars "def", Chars "abc" :<>: Chars "abc", Chars "abc" :<>: Empty, Chars "abc" :<>: None
             , Star (Chars "a"), Star (Chars "ab") ]
        ss = [ "", "a", "ab", "ad", "bd", "be", "c", "f", "aa", "aaaaaaa", "abbbb", "ababab" ]

--------------------------------------------------------------------------------

checkEmpty, checkNonEmpty :: GRegex -> Assertion

checkEmpty r = assertBool (show r ++ " can accept the empty string") (hasEmpty r)

checkNonEmpty r = assertBool (show r ++ " cannot accept the empty string") (not (hasEmpty r))


test4, test5, test6 :: Test

test4 = test $ map checkEmpty empties ++ map checkNonEmpty nonEmpties where
  empties = [Empty]
  nonEmpties = [None, Chars [], Chars "abc"]

test5 = test $ map checkEmpty empties ++ map checkNonEmpty nonEmpties where
  empties = [Chars "abc" :\/: Empty, Not (Chars "abc"), Empty :\/: Empty, None :\/: Empty
            , Chars "abc" :\/: (Empty :\/: Chars "def"), Not (Chars "abc") :/\: (Empty :\/: Chars "de")
            , Not (Empty :/\: Chars "ab")]
  nonEmpties = [Empty :/\: Chars "ab", Chars "ab" :\/: (Empty :/\: Chars "ab"), Not Empty, None :/\: Empty]

test6 = test $ map checkEmpty empties ++ map checkNonEmpty nonEmpties where
  empties = [Empty :<>: Empty, Star (Chars "ab"), Empty :<>: Star (Chars "ab"), Star (Chars "ab") :<>: Star (Chars "de")]
  nonEmpties = [Empty :<>: Chars "ab", Chars "ab" :<>: Empty, Star (Chars "a") :<>: Chars "a", Chars "a" :<>: Star (Chars "a")]

--------------------------------------------------------------------------------

test7, test8, test9 :: Test

test7 = test [ checkRegexEquiv r' p ss  | (r, p, c) <- rs, let r' = derivc c r]
  where rs = [ (None, None, c) | c <- ['a' .. 'l']] ++
             [ (Empty, None, c) | c <- ['a' .. 'l']] ++
             [ (Chars ['a'..'f'], Empty, c) | c <- ['a' .. 'f']] ++
             [ (Chars ['a'..'f'], None, c) | c <- ['g' .. 'l']]
        ss = [ "", "a", "ab", "ad", "bd", "be", "c", "f", "aa", "aaaaaaa", "abbbb", "ababab" ]

test8 = test [ checkRegexEquiv r' p ss  | (r, p, c) <- rs, let r' = derivc c r ]
  where rs = [ (Chars ['a' .. 'f'] :/\: Chars ['d' .. 'j'], Empty, c) | c <- ['d'..'f']] ++
             [ (Chars ['a' .. 'f'] :/\: Chars ['d' .. 'j'], None, c) | c <- ['a'..'c'] ++ ['g'..'l']] ++
             [ (Chars ['a' .. 'f'] :\/: Chars ['d' .. 'j'], Empty, c) | c <- ['a'..'j']] ++
             [ (Chars ['a' .. 'f'] :\/: Chars ['d' .. 'j'], None, c) | c <- ['k'..'l']] ++
             [ (Not (Chars ['a' .. 'f']), Not Empty, c) | c <- ['a'..'f']] ++
             [ (Not (Chars ['a' .. 'f']), Not None, c) | c <- ['g'..'l']] ++
             [ (Not (Chars ['a' .. 'f'] :/\: Chars ['d' .. 'j']), Not Empty, c) | c <- ['d'..'f']] ++
             [ (Not (Chars ['a' .. 'f'] :/\: Chars ['d' .. 'j']), Not None, c) | c <- ['a'..'c'] ++ ['g'..'l']] ++
             [ (Not (Chars ['a' .. 'f'] :\/: Chars ['d' .. 'j']), Not Empty, c) | c <- ['a'..'j']] ++
             [ (Not (Chars ['a' .. 'f'] :\/: Chars ['d' .. 'j']), Not None, c) | c <- ['k'..'l']]
        ss = [ "", "a", "ab", "ad", "bd", "be", "c", "f", "aa", "aaaaaaa", "abbbb", "ababab" ]

test9 = test [ checkRegexEquiv r' p ss  | (r, p, c) <- rs, let r' = derivc c r ]
  where rs = [ (Chars "abc" :<>: Chars "def", Chars "def", c ) | c <- ['a'..'c']] ++
             [ (Chars "abc" :<>: Chars "def", None, c ) | c <- ['d'..'l']] ++
             [ (Star (Chars "abc"), Star (Chars "abc"), c) | c <- ['a'..'c']] ++
             [ (Star (Chars "abc"), None, c) | c <- ['d'..'f']] ++
             [ (Star (Chars "abc" :<>: Chars "bcd"), Chars "bcd" :<>: Star (Chars "abc" :<>: Chars "bcd"), c) | c <- "abc" ] ++
             [ (Star (Chars "abc") :<>: Chars "d", Star (Chars "abc") :<>: Chars "d", c) | c <- "abc"] ++
             [ (Star (Chars "abc") :<>: Chars "d", Empty, 'd')]
        ss = [ "", "a", "ab", "ad", "bd", "be", "c", "f", "aa", "aaaaaaa", "abbbb", "ababab", "aaad", "d", "abcabcd" ]

--------------------------------------------------------------------------------

test10 :: Test

test10 = test [ checkRegexEquiv r' p ss  | (r, p, s) <- rs, let r' = deriv s r ]
  where rs = [ (Chars "abc" :<>: Chars "def", Empty, "ad")
             , (Chars "abc" :<>: Star (Chars "def"), Star (Chars "def"), "cdeee")
             , (Star (Chars "abc") :<>: Chars "abc", (Star (Chars "abc") :<>: Chars "abc" :\/: Empty), "ac") ]
        ss = [ "", "a", "ab", "ad", "bd", "be", "c", "f", "aa", "aaaaaaa", "abbbb", "ababab", "aaad", "d", "abcabcd" ]


--------------------------------------------------------------------------------
-- main
--------------------------------------------------------------------------------

allTests :: [(Int, Test)]
allTests = zip [1..] [test1, test2, test3, test4, test5, test6, test7, test8, test9, test10]

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
