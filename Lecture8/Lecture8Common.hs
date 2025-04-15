module Lecture8Common where

{-------------------------------------------------------------------------------

lecture 8
---------

Common functions for all of the lecture 8 developments.

-------------------------------------------------------------------------------}


-- The `try` abstracts the pattern of transforming a `Maybe` value, returning a
-- default if the `Maybe` value is `Nothing`.
try :: Maybe a -> (a -> b) -> Maybe b -> Maybe b
try (Just x) f _ = Just (f x)
try Nothing _ k  = k

-- The binary congruence rule, abstracted over the step function.
binaryCongGeneric :: (a -> Maybe a) -> (a -> a -> a) -> a -> a -> Maybe a
binaryCongGeneric step f m n = try (step m) (\m' -> f m' n) $
                               try (step n) (f m) $
                               Nothing                   

-- Traced iteration, again abstracted over the step function
untilNothing :: (a -> Maybe a) -> a -> [a]
untilNothing step x = x : steps (step x) where
  steps Nothing = []
  steps (Just y) = y : steps (step y)


-- Prints a list of things, one thing per line
prints :: Show a => [a] -> IO ()
prints = mapM_ print 