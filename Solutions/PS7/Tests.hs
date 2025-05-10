module Tests (module Tests) where

import Control.Monad
import Data.List (partition)
import Data.Maybe
import System.Exit ( exitWith, ExitCode(ExitFailure, ExitSuccess) )
import System.Environment ( getArgs )
import System.Random
import Test.HUnit
import Text.Read (readMaybe)
import Prelude hiding (and, or)
import Problems7

--------------------------------------------------------------------------------
-- tests
--------------------------------------------------------------------------------

tests1, tests2, tests3, tests4 :: Test

tests1 = test [
  t                @?= True,
  f                @?= False,
  neg t            @?= f,
  neg f            @?= t,
  and t t          @?= t,
  and f f          @?= f,
  and t f          @?= f,
  and f t          @?= f,
  or t t           @?= t,
  or t f           @?= t,
  or f t           @?= t,
  or f f           @?= f
  ]

tests2 = test [
  implies t t      @?= t,
  implies t f      @?= f,
  implies f t      @?= t,
  implies f f      @?= t,
  xor t t          @?= f,
  xor t f          @?= t,
  xor f t          @?= t,
  xor f f          @?= f,
  nand t t         @?= f,
  nand t f         @?= t,
  nand f t         @?= t,
  nand f f         @?= t
  ]

data AST = Val QBF | Vars String | Neg AST | And AST AST | Or AST AST | Forall String AST | Exists String AST

subs :: AST -> String -> QBF -> AST
subs (Val q) _ _ = (Val q)
subs (Vars s) x q = if (s == x) then (Val q) else (Vars s)
subs (Neg ast) x q = Neg (subs ast x q)
subs (And ast1 ast2) x q = And (subs ast1 x q) (subs ast2 x q)
subs (Or ast1 ast2) x q = Or (subs ast1 x q) (subs ast2 x q)
subs (Forall s ast) x q = if (s == x) then (Forall s ast) else (Forall s (subs ast x q))
subs (Exists s ast) x q = if (s == x) then (Exists s ast) else (Exists s (subs ast x q))

toQBF :: Bool -> QBF
toQBF True = t
toQBF False = f

evaluateAssignment :: AST -> Proof -> QBF
evaluateAssignment (Val q) _ = q
evaluateAssignment (Vars s) _ = f
evaluateAssignment (Neg x) p = neg (evaluateAssignment x p)
evaluateAssignment (And x y) p = (evaluateAssignment x p) `and` (evaluateAssignment y p)
evaluateAssignment (Or x y) p = (evaluateAssignment x p) `or` (evaluateAssignment y p)
evaluateAssignment (Forall s x) (Branch tt ff) = (evaluateAssignment (subs x s t) tt) `and` (evaluateAssignment (subs x s f) ff)
evaluateAssignment (Forall s x) _ = f
evaluateAssignment (Exists s x) (Assignment []) = f
evaluateAssignment (Exists s x) (Assignment (y:ys)) = (evaluateAssignment (subs x s (toQBF y)) (Assignment (ys)))
evaluateAssignment (Exists s x) _ = f

runEvaluation :: AST -> Response -> [Bool]
runEvaluation ast NotTrue = [False]
runEvaluation ast (IsTrue p) = [True, evaluateAssignment ast p]

tree1 = Exists "x1" (Exists "x2" (Exists "x3" (And (And (Vars "x1") (Vars "x3")) (Vars "x3"))))
-- ∀ y. ∃ x. (x ∨ ¬ y)
tree2 = Forall "y" (Exists "x" (Or (Vars "x") (Neg (Vars "y"))))
-- ∀ y. ∃ x. (y ∧ ¬ x)
tree3 = Forall "y" (Exists "x" (And (Vars "y") (Neg (Vars "x"))))
-- ∀ y. ∃ x₁. ∃ x₂. (y ∨ (x₁ ∧ x₂))
tree4 = Forall "y" (Exists "x1" (Exists "x2" (Or (Vars "y") (And (Vars "x1") (Vars "x2")))))
-- ∀ y₁. ∀ y₂. ∃ x. ((y₁ ∨ y₂) ∧ x)
tree5 = Forall "y1" (Forall "y2" (Exists "x" (And (Or (Vars "y1") (Vars "y2")) (Vars "x"))))

tests3 = test [
  runEvaluation tree1 (IsTrue (Assignment [True , True , True]))      @?= [True, True],
  runEvaluation tree2 p2                                              @?= [True, True],
  runEvaluation tree3 p3                                              @?= [False],
  runEvaluation tree4 p4                                              @?= [True, True],
  runEvaluation tree5 p5                                              @?= [False]
  ]

tests4 = test [
  forAll (\ x -> t `or` x)                                            @?= t,
  forAll (\ x -> exists (\ y -> x `and` y))                           @?= f,
  forAll (\ x -> x `and` t)                                           @?= f,
  exists (\ x -> x)                                                   @?= t,
  forAll (\ x -> x)                                                   @?= f,
  exists (\ x -> exists (\ y -> x `and `y))                           @?= t,
  forAll (\ x -> exists (\ y -> exists (\ z -> (x `or` z) `and` y)))  @?= t,
  forAll (\ y -> exists (\ x -> exists (\ z -> (x `or` z) `and` y)))  @?= f
  ]

--------------------------------------------------------------------------------
-- main
--------------------------------------------------------------------------------

allTests :: [(Int, Test)]
allTests = zip [1..] [tests1, tests2, tests3, tests4]

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
