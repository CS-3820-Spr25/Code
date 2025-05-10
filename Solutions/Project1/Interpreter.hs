module Interpreter (interpret) where

import Language

import Graphics.Rendering.Cairo hiding (x)
import qualified Text.Megaparsec.Char.Lexer as L
import Data.List
import Data.Ratio

-- The state is the current object list, the stack, and the directory
data State = State [PSExpr] [PSExpr] [Dictionary]

instance Show State where
  show (State c s _) = cstr ++ "\n" ++ sstr
    where
      cstr = case c of
        [] -> " Execution stack empty."
        _  -> " Execution Stack:\n  " ++ concat (intersperse "\n  " (map show c))
      sstr = case s of
        [] -> " Data stack empty."
        _  -> " Data Stack:\n  " ++ concat (intersperse "\n  " (map show s))

emptyState :: State
emptyState = State [] [] []

interpret :: PSExpr -> Render (Result State)
interpret (PSProcedure cmds) = bigStepPs $ State cmds [] [[], sysdict]
interpret _ = return $ Left ("Unexpected toplevel symbol", emptyState)

lookupInDicts :: [Dictionary] -> String -> Maybe PSExpr
lookupInDicts [] _ = Nothing
lookupInDicts (x:xs) name = case lookup name x of
  Just e -> Just e
  Nothing -> lookupInDicts xs name

-- Manual monomorphisation because of wrong rank
binNumOp :: (Rational -> Rational -> Rational) -> State -> Result State
binNumOp dop (State c ((PSRational i):(PSRational j):s) d) =
  Right (State c ((PSRational $ dop j i):s) d)
binNumOp _ s = Left ("Illegal arguments to binary operator.", s)

-- Helper for unary arithmetic operators
unaryNumOp :: (Rational -> Rational ) -> State -> Result State
unaryNumOp iop (State c ((PSRational i):s)  d) = Right (State c ((PSRational $ iop i):s) d)
unaryNumOp _ s = Left ("Illegal arguments to unary operator.", s)

-- Helper to handle the case where a recursion can fail
tryRecurse :: Result State -> Render (Result State)
tryRecurse r@(Left _) = return r
tryRecurse (Right s) = bigStepPs s

bigStepPs :: State -> Render (Result State)
bigStepPs s@(State [] _ _) = return $ Right s

-- We convert all integers to rational numbers
bigStepPs (State ((PSInt i):c) s d) = bigStepPs (State c ((PSRational (fromIntegral i)):s) d)

bigStepPs (State (r@(PSRational _):c)    s d) = bigStepPs (State c (r:s) d)
bigStepPs (State (b@(PSBoolean _):c)     s d) = bigStepPs (State c (b:s) d)
bigStepPs (State (a@(PSArray _):c)       s d) = bigStepPs (State c (a:s) d)
bigStepPs (State (p@(PSProcedure _):c)   s d) = bigStepPs (State c (p:s) d)

bigStepPs (State (b@(PSLiteralName _):c) s d) = bigStepPs (State c (b:s) d)

bigStepPs s@(State ((PSExecutableName n):cmds) stack dicts) =
  case lookupInDicts dicts n of
    Just (PSProcedure scmds) -> bigStepPs (State (scmds ++ cmds) stack dicts)
    Just e -> bigStepPs (State (e:cmds) stack dicts)
    Nothing ->  return $ Left ("name not found: " ++ n, s)

bigStepPs (State (PSOp PSdup:c)  (a:s) d)   = bigStepPs $ State c (a:a:s) d
bigStepPs (State (PSOp PSpop:c)  (_:s) d)   = bigStepPs $ State c      s  d
bigStepPs (State (PSOp PSexch:c) (a:b:s) d) = bigStepPs $ State c (b:a:s) d
bigStepPs (State (PSOp PSadd:c) s d) = tryRecurse $ binNumOp (+) (State c s d)
bigStepPs (State (PSOp PSsub:c) s d) = tryRecurse $ binNumOp (-) (State c s d)
bigStepPs (State (PSOp PSmul:c) s d) = tryRecurse $ binNumOp (*) (State c s d)
bigStepPs (State (PSOp PSdiv:c) ((PSRational j):(PSRational i):s) d) =
  bigStepPs (State c (PSRational (i / j):s) d)

bigStepPs st@(State (PSOp PSidiv:c) ((PSRational j):(PSRational i):s) d)
  | denominator j /= 1 || denominator i /= 1 = return $ Left ("idiv on non-integers", st)
  | otherwise = bigStepPs (State c (PSRational (fromIntegral $ (numerator i) `div` (numerator j)):s) d)
bigStepPs st@(State (PSOp PSmod:c)  ((PSRational j):(PSRational i):s) d)
  | denominator j /= 1 || denominator i /= 1 = return $ Left ("idiv on non-integers", st)
  | otherwise = bigStepPs (State c (PSRational (fromIntegral $ (numerator i) `mod` (numerator j)):s) d)

bigStepPs (State (PSOp PSabs:c) s d)      = tryRecurse $ unaryNumOp (abs) (State c s d)
bigStepPs (State (PSOp PSneg:c) s d)      = tryRecurse $ unaryNumOp (0.0 -) (State c s d)
bigStepPs (State (PSOp PSround:c) s d)    = tryRecurse $ unaryNumOp (fromIntegral . round)    (State c s d)
bigStepPs (State (PSOp PStruncate:c) s d) = tryRecurse $ unaryNumOp (fromIntegral . truncate) (State c s d)

bigStepPs (State (PSOp PSsin:c) ((PSRational i):s) d) =
  bigStepPs (State c (PSRational (realToFrac (sin $ (fromRational i) / 180 * pi)):s) d)
bigStepPs (State (PSOp PScos:c) ((PSRational i):s) d) =
  bigStepPs (State c (PSRational (realToFrac (cos $ (fromRational i) / 180 * pi)):s) d)

bigStepPs (State (PSOp PSeq:c) (b:a:s) d) = bigStepPs (State c (PSBoolean (a == b):s) d)
bigStepPs (State (PSOp PSgt:c) (b:a:s) d) = bigStepPs (State c (PSBoolean (a > b):s) d)
bigStepPs (State (PSOp PSge:c) (b:a:s) d) = bigStepPs (State c (PSBoolean (a >= b):s) d)

bigStepPs (State (PSOp PSnot:c) ((PSBoolean a):s) d) = bigStepPs (State c (PSBoolean (not a):s) d)
bigStepPs (State (PSOp PSand:c) ((PSBoolean b):(PSBoolean a):s) d) = bigStepPs (State c (PSBoolean (a && b):s) d)
bigStepPs (State (PSOp PSor:c)  ((PSBoolean b):(PSBoolean a):s) d) = bigStepPs (State c (PSBoolean (a || b):s) d)

bigStepPs (State (PSOp PSifelse:c) (PSProcedure no:PSProcedure yes:PSBoolean cond:s) d)
  | cond      = bigStepPs $ State (yes ++ c) s d
  | otherwise = bigStepPs $ State (no ++ c) s d

bigStepPs (State (PSOp PSrepeat:c) (PSProcedure code:PSRational n:s) d) = bigStepPs $ State c' s d
  where c' = (concat $ ((take . floor . fromRational) n) (repeat code)) ++ c

bigStepPs (State (PSOp PSnewpath:c) s d) = newPath >> (bigStepPs $ State c s d)

bigStepPs (State (PSOp PSmoveto:c) ((PSRational y):(PSRational x):s) d) =
  moveTo (fromRational x) (fromRational y) >> (bigStepPs $ State c s d)

bigStepPs (State (PSOp PSclosepath:c) s d) = closePath >> (bigStepPs $ State c s d)

bigStepPs (State (PSOp PSlineto:c) ((PSRational y):(PSRational x):s) d) =
  lineTo (fromRational x) (fromRational y) >> (bigStepPs $ State c s d)

bigStepPs (State (PSOp PSsetlinewidth:c) ((PSRational w):s) d) =
  setLineWidth (fromRational w) >> (bigStepPs $ State c s d)

bigStepPs (State (PSOp PSstroke:c) s d)     = stroke >> (bigStepPs $ State c s d)
bigStepPs (State (PSOp PSfill:c) s d)       = fill >> (bigStepPs $ State c s d)

bigStepPs (State (PSOp PSsetrgbcolor:c) ((PSRational b):(PSRational g):(PSRational r):s) d) =
  setSourceRGB (fromRational r) (fromRational g) (fromRational b) >> (bigStepPs $ State c s d)

-- Dict stuff
bigStepPs (State (PSOp PSdict:c)         (_:s) d) = (bigStepPs $ State c (PSDict []:s) d)
bigStepPs (State (PSOp PSbegin:c) (PSDict x:s) d) = (bigStepPs $ State c s (x:d))

bigStepPs (State (PSOp PSdef:c)   (v:(PSLiteralName n):s) (d:ds)) = (bigStepPs $ State c s (((n, v):d):ds))

bigStepPs s = return $ Left ("not implemented", s)
