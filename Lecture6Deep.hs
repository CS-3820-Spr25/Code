module Lecture6Deep where

import Prelude hiding ((<>), (<|>), words)
import Data.List ((\\))

{-------------------------------------------------------------------------------

The idea here is a deep embedding of regular expressions in Haskell.

Again, we're not going to worry about named groups or anything---we're just
trying to return a Boolean answer of whether or not a string matches a regex.

One question that arises immediately is how much information to capture in our
deep embedding.  For example, we know (from prior discussion of regular
expressions) that r? ≡ empty <|> r.  Should we include ? as a distinct node in
our abstract syntax.

 - If we don't, that will simplify interpretations like matching strings against
   regular expressions, or enumerating a regex's language, because we'll have
   fewer cases.
 - If we do, we more accurately preserve the original regex for interpretations
   like printing.

For now, we'll keep everything---we can always rely on equations like the above
in our implementations.

-------------------------------------------------------------------------------}

data Regex =
    AnyChar | Chars [Char] | NotChars [Char] |
    Regex :|: Regex | Empty |
    Regex :<>: Regex | None |
    Question Regex | Plus Regex | Star Regex

-- An aside about syntax: Just like Haskell has infix operators (+, - *), it has
-- infix constructors (:, :<>:).  You can tell an infix constructor because it
-- *starts* with a colon.  It doesn't have to end with one, although it is
-- common in practice.

--------------------------------------------------------------------------------
-- We can't interpret regular expressions yet, but we can define some.  Here are
-- the examples from our previous discussion... identical modulo capitalization
-- and colons.

upper, lower, space :: Regex
upper = Chars ['A'..'Z']
lower = Chars ['a'..'z']
space = Chars [' ', '\t', '\r', '\n']

capWord, capWords :: Regex
capWord = upper :<>: Star lower
capWords = Plus (capWord :<>: Plus space)

word, words :: Regex
word = capWord :|: Plus lower
words = Plus (word :<>: Plus space)

{-------------------------------------------------------------------------------

Now let's do something with our regular expression type.  One thing we might
want to do is print them out---that is to say, transform regular expressions
into strings.   We can do this by writing a function that takes a regular
expression as an argument.  This is no different from the pattern matching
examples we've seen before, just with more cases.

We have a small detail here.  We've added a couple of non-standard regular
expressions, one for the empty string and one that always fails.  As tempting as
it is to print these out as ɛ and ∅, to avoid issues with unicode output we'll
print them out as e and 0.

-------------------------------------------------------------------------------}

format :: Regex -> String
format AnyChar       = "."
format (Chars ds)    = "[" ++ ds ++ "]"
format (NotChars ds) = "[^" ++ ds ++ "]"
format (r :|: r')    = parens (format r) ++ "|" ++ parens (format r')
format None          = "0"
format (r :<>: r')   = format r ++ format r'
format Empty         = "e"
format (Question r)  = parens (format r) ++ "?"
format (Plus r)      = parens (format r) ++ "+"
format (Star r)      = parens (format r) ++ "*"

parens :: String -> String
parens s = "(" ++ s ++ ")"

-- >>> format capWords
-- "([ABCDEFGHIJKLMNOPQRSTUVWXYZ]([abcdefghijklmnopqrstuvwxyz])*([ \t\r\n])+)+"

-- You might notice that we're pretty aggressive in placing parentheses.  Of
-- course, we could do better.. but (at least in the general case) we'd be
-- likely to need some additional context.

{-------------------------------------------------------------------------------

Now we'll return to the interpretations of regular expressions from the previous
embedding.  Let's define our alphabet.

-------------------------------------------------------------------------------}

alphabet :: [Char]
alphabet = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ [' ', '\r', '\t', '\n']

{-------------------------------------------------------------------------------

Now, let's define a function to enumerate the strings in a regex's
language---this is our first semantics we explored as a shallow embedding.  In
the format function, we wanted to represent each different regular expression
construction, but here we can start to fall back on our understanding of
equivalent regular expressions.

-------------------------------------------------------------------------------}

enumerate :: Regex -> [String]
enumerate AnyChar       = enumerate (Chars alphabet)
enumerate (Chars cs)    = map singleton cs
  where singleton c = [c]
enumerate (NotChars cs) = enumerate (Chars (alphabet \\ cs))
enumerate (r :<>: r')   = concatMap (add r') (enumerate r)
  where add r' s = map (s ++) (enumerate r')
enumerate None          = []
enumerate (r :|: r')    = enumerate r ++ enumerate r'
enumerate Empty         = [""]
enumerate (Question r)  = enumerate (Empty :|: r)
enumerate (Star r)      = enumerate (Question (Plus r))
enumerate (Plus r)      = enumerate (r :<>: Star r)


-- >>> enumerate (Chars ['A','B'] :<>: Chars ['a','b'])
-- ["Aa","Ab","Ba","Bb"]

-- >>> take 20 (enumerate capWord)
-- ["A","Aa","Aaa","Aaaa","Aaaaa","Aaaaaa","Aaaaaaa","Aaaaaaaa","Aaaaaaaaa","Aaaaaaaaaa","Aaaaaaaaaaa","Aaaaaaaaaaaa","Aaaaaaaaaaaaa","Aaaaaaaaaaaaaa","Aaaaaaaaaaaaaaa","Aaaaaaaaaaaaaaaa","Aaaaaaaaaaaaaaaaa","Aaaaaaaaaaaaaaaaaa","Aaaaaaaaaaaaaaaaaaa","Aaaaaaaaaaaaaaaaaaaa"]

{-------------------------------------------------------------------------------

We can define infinite sets in Haskell, but they're hard to work with.  Instead,
let's captures sets by their *characteristic functions*: a subset of X is
equivalent to a function from X to Booleans.

-------------------------------------------------------------------------------}

recognizes :: Regex -> String -> Bool

-- We start with character classes: the regex [cs] recognizes strings that are
-- exactly one of the characters of cs.
recognizes (Chars cs)    [c] = c `elem` cs
recognizes (Chars cs)    s = False  

-- As above, we can interpret the AnyChar and NotChars regexes in terms of Chars
recognizes AnyChar       s = recognizes (Chars alphabet) s
recognizes (NotChars cs) s = recognizes (Chars (alphabet \\ cs)) s

-- The `None` regex recognizes no strings, while `r :|: p` matches a string if
-- either `r` or `p` recognizes it.  Note that `r :|: Empty = r`, and `b ||
-- false = b`.
recognizes None          s = False
recognizes (r :|: p)     s = recognizes r s || recognizes p s

-- The `Empty` regex recognizes exactly the empty string
recognizes Empty         s = null s

-- The regex `r :<>: p` recognizes a string if it breaks into `s ++ t` such that
-- `r` recognizes `s` and `p` recognizes `t`.  The challenge is finding where to
-- break the string; as a brute force approach, let's try every possibility.
recognizes (r :<>: p)    s = any recognizesBoth ss
  where ss = splits s 
        recognizesBoth (s1, s2) = recognizes r s1 && recognizes p s2

        splits :: String -> [(String, String)]
        splits s = map split [0..length s] where
          split i = splitAt i s

-- Our interpretation of these is unchanged from the other interpretations.
recognizes (Question r)  s = recognizes (Empty :|: r) s
recognizes (Plus r)      s = recognizes (r :<>: Star r) s
recognizes (Star r)      s = recognizes (Question (Plus r)) s


{-------------------------------------------------------------------------------

That idea avoided the infinite sets, but is still awkward to implement: we have
to figure out where to break strings, and that's going to lead to a lot of
wasted effort.  For our final attempt, let's build the idea of splitting into
the idea of the meaning of a regular expression.  That is:

We interpret regex r as a function from an input s to a list of the strings that
follow a string accepted by r in s.

It may take a minute to wrap your head around that.  Here are a few examples:

    remains AnyChar "foo" = ["oo"]

AnyChar has to accept the first character in "foo", so the only possible
remainder is "oo".

    remains AnyChar "" = []

AnyChar has to accept some character; if there's no character to accept, then
there are no possible remainders.

    remains (Star upper) "ABC" = ["ABC", "BC", "C", ""]

upper accepts upper case letters; Star upper accepts any number of them.  So the
remainder after star upper can be any tail of the original string.

-------------------------------------------------------------------------------}

remains :: Regex -> String -> [String]
remains (Chars ds) []   = []
remains (Chars ds) (c : cs)
  | c `elem` ds         = [cs]
  | otherwise           = []

remains AnyChar s       = remains (Chars alphabet) s
remains (NotChars cs) s = remains (Chars (alphabet \\ cs)) s

---------------------------------------------------------------------------------
-- Alternation (r|s) accepts *either* the strings accepted by *r* or those
-- accepted by *s*, so the unaccepted remainders are all the unaccepted
-- remainders of *r* and the unaccepted remainders of *s*.  The unit here is the
-- regular expression that always fails; that is, it has no remainders.

remains (r :|: r') s    = remains r s ++ remains r' s
remains None s          = []

--------------------------------------------------------------------------------
-- Finally, the interesting case: what to do about concatenation?  The regular
-- expression (rs) succeeds if r accepts some portion of the string, and then s
-- accepts the remainder of the string.  We can express this in our idea of
-- regular expressions as follows: We want the strings remaining after running s
-- on each of the strings remaining after r.  The unit accepts the empty string,
-- so the remainder is the whole original string.

remains (r :<>: r') s   = concatMap (remains r') (remains r s)
remains Empty s         = [s]


remains (Question r) s  = remains (Empty :|: r) s
remains (Plus r) s      = remains (r :<>: Star r) s
remains (Star r) s      = remains (Question (Plus r)) s

-- And now we can define the matching test on top

match :: Regex -> String -> Bool
match r s = "" `elem` remains r s

-- >>> remains capWords "This Is a test"
-- ["Is a test","a test"]

-- >>> match capWords "This is a test"
-- False

-- >>> match capWords "This Is A Test "
-- True
