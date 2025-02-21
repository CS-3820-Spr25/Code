{-# LANGUAGE StandaloneDeriving #-}
module Tests (module Tests) where

import Data.Char (ord)
import Data.List (partition, sort, sortBy, foldr1)
import System.Exit ( exitWith, ExitCode(ExitFailure, ExitSuccess) )
import System.Environment ( getArgs )
import Test.HUnit
import Text.Read (readMaybe)

import Problems4

--------------------------------------------------------------------------------
-- Binary trees

deriving instance Eq a => Eq (BinTree a)

bt0, bt2, bt3 :: BinTree Int 
bt0 = LeafB
bt2 = BranchB 4 (BranchB 1 (BranchB 5 LeafB LeafB) LeafB) (BranchB 1 LeafB (BranchB 6 LeafB LeafB))
bt3 = btFromList [1..30] where

btFromList :: [a] -> BinTree a
btFromList xs = fst (go (length xs) xs) where
  go 0 xs = (LeafB, xs)
  go n xs = (BranchB y l r, zs) where
    halfn = (n - 1) `div` 2
    halfn' | odd n     = halfn
           | otherwise = halfn + 1
    (l, y : ys) = go halfn' xs
    (r, zs) = go halfn ys

reverseBT :: BinTree a -> BinTree a
reverseBT LeafB           = LeafB
reverseBT (BranchB x l r) = BranchB x (reverseBT r) (reverseBT l)

valuesFrom :: BinTree a -> [a]
valuesFrom LeafB = []
valuesFrom (BranchB x l r) = valuesFrom l ++ x : valuesFrom r             
        
test1, test2, test3 :: Test

test1 = test [ sumBT bt0 ~?= 0
             , sumBT bt1 ~?= 12
             , sumBT bt2 ~?= 17
             , sumBT bt3 ~?= 465
             , sumBT (reverseBT bt3) ~?= 465
             , sumBT (btFromList [-30..30]) ~?= 0
             , sumBT (reverseBT (btFromList [-30..30])) ~?= 0 ]

test2 = test [ insertBT 1 bt0 ~?= BranchB 1 LeafB LeafB
             , insertBT 1 bt1 ~?= bt1
             , insertBT 1 (BranchB 1 LeafB LeafB) ~?= BranchB 1 LeafB LeafB
             , insertBT 1 (BranchB 2 LeafB (BranchB 3 LeafB LeafB)) ~?= BranchB 2 (BranchB 1 LeafB LeafB) (BranchB 3 LeafB LeafB)
             , insertBT 1 (BranchB 0 LeafB (BranchB 2 LeafB LeafB)) ~?= BranchB 0 LeafB (BranchB 2 (BranchB 1 LeafB LeafB) LeafB)
             , insertBT 1 (BranchB 2 (BranchB 0 LeafB LeafB) (BranchB 3 LeafB LeafB)) ~?= BranchB 2 (BranchB 0 LeafB (BranchB 1 LeafB LeafB)) (BranchB 3 LeafB LeafB)
             , valuesFrom (insertBT 0 (btFromList [1..20])) ~?= [0..20]
             , valuesFrom (foldr insertBT LeafB [0..30]) ~?= [0..30]
             , valuesFrom (foldr insertBT LeafB (shuffle [0..29])) ~?= [0..29]
             ]
  where shuffle xs = go xs [] where
          go [] ys = ys
          go (x : y : xs) ys = x : go xs (y : ys)

test3 = test [ mapBT (1+) bt2 ~?= BranchB 5 (BranchB 2 (BranchB 6 LeafB LeafB) LeafB) (BranchB 2 LeafB (BranchB 7 LeafB LeafB))
             , mapBT even bt2 ~?= BranchB True (BranchB False (BranchB False LeafB LeafB) LeafB) (BranchB False LeafB (BranchB True LeafB LeafB))
             , mapBT (2*) (btFromList [0..20]) ~?= btFromList [0,2..40]
             , mapBT ord (btFromList ['a'..'z']) ~?= btFromList [97..122] ]          

--------------------------------------------------------------------------------
-- Rose trees             

rt2, rt3 :: RoseTree Int

rt2 = BranchR 1 [BranchR n [] | n <- [2..40]]

rt3 = build [3, 5, 7, 9, 11] where
  build [] = BranchR 1 []
  build (n : ns) = BranchR 1 (replicate n t) where t = build ns

products [] = 1
products (n : ns) = 1 + n * products ns

test4, test5 :: Test

test4 = test [ sumRT rt1 ~?= sum [1..10] 
             , sumRT rt2 ~?= sum [1..40]
             , sumRT rt3 ~?= products [3,5,7,9,11]]

test5 = test [ flattenRT rt1 ~?= [1..10]
             , flattenRT rt2 ~?= [1..40]
             , length (flattenRT rt3) ~?= products [3,5,7,9,11]]

--------------------------------------------------------------------------------
-- Tries

test6, test7, test8 :: Test

tr2 :: Trie  
tr2 = BranchT True [("p",BranchT False [("ick",BranchT True [("le",BranchT True [])]),("a",BranchT False [("ir",BranchT True []),("r",BranchT True [("rot",BranchT True [])])])])]

someStrings :: [String]
someStrings = ["hawk", "hawkeye", "hawkeyes", "helicopter", "helios", "pickle", "pick", "pair", "par", "parrot", "halestorm", ""]


test6 = test [memberT s t ~?= b | (t, bs) <- ps, (s, b) <- zip someStrings bs] where
  ps = [ (tr1, [True, True, True, True, True, False, False, False, False, False, False, False])
       , (tr2, [False, False, False, False, False, True, True, True, True, True, False, True]) ]


test7 = test $
  [ commonPrefix "Hello, everyone!" "Hello, world!" ~?= "Hello, "
  , commonPrefix "Star Wars" "Star Trek"            ~?= "Star "
  , commonPrefix "Radiohead" "The Decemberists"     ~?= ""
  , commonPrefix "" "Boop"                          ~?= ""
  , commonPrefix "Snoot" ""                         ~?= ""
  , commonPrefix "Zahnzusatzversicherung"
                 "Zahnzusatzversicherung"           ~?= "Zahnzusatzversicherung"
  ]

deriving instance Eq Trie

test8 = test $
  [ norm (insertT "umbrella" t1) ~?= norm t2
  , sort (strings (insertT "pleiades" t1)) ~?= ["paper", "plant", "pleiades"]
  , norm (insertT "plant" (insertT "paper" empty)) ~?= norm t1
  , norm (insertT "paper" (insertT "plant" empty)) ~?= norm t1
  , norm (insertT "plant" t1) ~?= norm t1
  , sort (strings (insertT "the white stripes" r1)) ~?= ["the decemberists", "the doors", "the mountain goats", "the white stripes"]
  , norm (insertT "mgmt" (insertT "modest mouse" r1)) ~?= norm r2
  ]
  where empty = BranchT False []

        norm :: Trie -> Trie
        norm (BranchT b ts) = BranchT b . sortBy h2 . map h1 $ ts
          where
          h1 (p, r) = (p, norm r)
          h2 (p1, _) (p2, _) = compare p1 p2
        
        strings :: Trie -> [String]
        strings = go [] where
          go cs (BranchT b bs) = here ++ concat (map (go' cs) bs) where
            here | b = [cs]
                 | otherwise = []
          go' cs (ds, t) = go (cs ++ ds) t
        
        unbranch :: Trie -> [(String, Trie)]
        unbranch (BranchT _ t) = t  -- I am unsure about this
        
        r1, r2 :: Trie
        r1 = BranchT False
               [("the "
                 , BranchT False
                     [("d", BranchT False
                              [ ("ecemberists", BranchT True [])
                              , ("oors", BranchT True [])])
                      , ("mountain goats", BranchT True []) ])]
        r2 = BranchT False $ unbranch r1 ++ [("m", BranchT False [("gmt", BranchT True []), ("odest mouse", BranchT True [])])]  

--------------------------------------------------------------------------------
-- main
--------------------------------------------------------------------------------

allTests :: [(Int, Test)]
allTests = zip [1..] [test1, test2, test3, test4, test5, test6, test7, test8]

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
