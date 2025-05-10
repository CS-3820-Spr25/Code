module Problems7 (module Problems7) where

import Prelude hiding (and, or, not)

{-------------------------------------------------------------------------------

CS:3820 Spring 2025 Problem Set 7
=================================

In lecture, we developed a shallow embedding of regular expressions in
Haskell. By a "shallow embedding", we mean that we render the syntax and meaning
of regular expressions (themselves a *language*) directly into Haskell
terms. For reference, we could have instead defined regular expressions as a
Haskell datatype:

  data Regex =
    Empty | Character Char | Regex <|> Regex |
    Regex <> Regex | star Regex

and then *evaluated* Regex terms to lists of strings.

  eval : Regex -> [String]
  eval = ...

If you contrast this approach with that of Lecture 6, you'll see that a shallow
embedding effectively "skips" the first step by encoding the primitives of
regular expressions directly and immediately in Haskell. So a deep embedding
will have an intermediate data type (e.g., Regex above) before evaluation; a
shallow embedding will immediately evaluate.

We will continue this concept, but for a different type of
**language**. Specifically, we will give a shallow embedding of Quantified
Boolean Formulae (QBF). Below is a data type we *would* use to represent a QBF
were we using a data type to represent it!

  data QBF =
   T | F | Var String |
   Neg QBF | And QBF QBF | Or QBF QBF |
   Forall String QBF | Exists String QBF

This data type can be used to represent formulae such as (respectively):
- Truth constants: T and F;
- Variables: x, y, z, and so forth;
- The negation of a formula: ¬ Q (read as "not Q" or "neg Q");
- The conjunction of two formulae: P ∧ Q (read as "P and Q");
- The disjunction of two formulae: P ∨ Q (read as "P or Q");
- The quantification over *all* formulae: ∀ x. P (read as "forAll x such that P");
- The quantification over *some* formulae: ∃ x. P (read as "there exists x such that P").

Ultimately, we would like to be able to answer, for an arbitrary formula Q,
if Q is **True**. For example, the formula

  ∀ x. T ∨ x

is true no matter what we select for x (T or F), and hence the formula is
designated to be **True**. Inversely, the formula

  ∃ x. ∀ y. x ∧ y

is **False**. Let us think this through: does there exists a Boolean x such
that, for all other Booleans y, we have that x ∧ y is true? The answer is no:

--------------------
x     | y     | x ∧ y
--------------------
T     | T     | T
T     | F     | F
F     | T     | F
F     | F     | F

For the formula to be true, we should see that one of the selections of `x` above
yields only true in the `x ∧ y`. Yet this is not the case, and so the formula is false.


-------------------------------------------------------------------------------}


{-------------------------------------------------------------------------------

Problem 1
--------------

As described above, our goal is to use a shallow embedding of Quantified
Boolean Formulae (QBF) in order to answer if arbitrary QBFs are **T** or
**F**.

We will approach this problem incrementally.  We first consider the easy case:
truth constants, negation, conjunction, and disjunction. We are going to choose
to represent boolean formulae by means of immediate evaluation—That is to say,
a formulae is simply a Bool value: -}

type QBF = Bool

{-

To give an example, the "representation" of

  T ∨ F

is just

  T

because T ∨ F equals T. Likewise, the representation of F ∧ T is just F.

Your first task is to define "constructors" for the QBF primitives of
T, F, negation, And, and Or. These should behave entirely as you expect them to.

NOTE: You cannot use the `and`, `or`, and `not` primitives from the Haskell
prelude. Instead, define these functions using pattern matching, guards, or
if/then/else.

-------------------------------------------------------------------------------}


t , f    :: QBF
neg      :: QBF -> QBF
and , or :: QBF -> QBF -> QBF


t = True
f = False

neg x   = if x then f else t
and x y = if x then y else f
or x y  = if x then t else y

{-------------------------------------------------------------------------------

Problem 2
--------------

Our next problem concerns encoding more elaborate formulae as simpler
ones. For example, it is well known that the implication

  P ⇒ Q

is equivalent (when P and Q are boolean formulae) to the formula

  ¬ P ∨ Q

This rule is known as **Material Implication**.

Implement a shallow embedding of implication below; your definition of `implies`
should use (some of) your definitions from problem 1.

Likewise, also define:
- `x xor y`, which is true if exactly one of `x` and `y` is true (but not both).
- `x nand y`, or "not and", which is false precisely when `x` and `y` are both true
  and true otherwise. See https://simple.wikipedia.org/wiki/NAND_gate


NOTE: You **must** use the primitives above to define the operators below. Your
implementations will be tested with respect to both correct implementations
**and themselves**. In other words: tests will fail if you define `implies`,
`xor`, or `nand` directly over booleans without the use of `and`, `or`, `t`, and
`f`.

-------------------------------------------------------------------------------}


implies , xor , nand :: QBF -> QBF -> QBF


implies x y = neg x `or` y
xor x y     = (x `and` (neg y)) `or` (neg x `and` y)
nand x y    = neg (x `and` y)

{-------------------------------------------------------------------------------

Problem 3
--------------

Next, provide some "proofs" that the given quantified formulae are true. Here a
"proof" should be a Tree of "assignments" to the *existentially quantified**
variables

  x₁, x₂, ... xₙ

such that, for each assignment to the **universally quantified** variables

  y₁, y₂, ... yₙ

the formula is true. We represent proofs as trees:
-}

data Proof = Branch Proof Proof | Assignment [Bool]

{-

For each ∀-quantified variable y, you will need to give two proofs: one for when
y is True and one for when y is False.  For example, a proof that the formula

  ∀ y. ∃ x₁. ∃ x₂. (x₁ ∨ y ∨ x₂)

is True would be:

-}

p :: Proof
p = Branch (Assignment [True, True]) (Assignment [False, False])

  
{-

The proof `p` states,
  - in the left branch, when y is True, that assigning True to both x₁ and x₂
    makes the formula
      (x₁ ∨ y ∨ x₂)
    true, and
  - In the right branch, when y is False, that assigning False to x₁ and x₂
    makes the formula
      (x ∨ y)
    true.

In other words, regardless of the value of y, we can give an assignment to x₁
and x₂ that makes the formula True. (Note that proofs are not **unique**: in the
right branch, we could have also let x₁ and x₂ be assigned True, and the formula
would have remained True.)


For each formula below, if the formula is True, return
  IsTrue p
where `p` is a proof. If the formula is not True, return NotTrue.

-------------------------------------------------------------------------------}


data Response = IsTrue Proof | NotTrue

p1 , p2 , p3 , p4 , p5 :: Response


-- p1 =  ∃ x₁. ∃ x₂. ∃ x₃. (x₁ `xor` x₃) `nand` x₃
p1 = IsTrue $ Assignment [True , True , True]

-- p2 = ∀ y. ∃ x. (x ⇒ ¬ y)
p2 = IsTrue $ Branch
  (Assignment [True]) -- (x ⇒ ¬ T)
  (Assignment [True]) -- (x ⇒ ¬ F)

-- p3 = ∀ y. ∃ x. (y ∧ ¬ x)
p3 = NotTrue

-- p4 = ∀ y. ∃ x₁. ∃ x₂. (y ∨ (x₁ ∧ x₂))
p4 = IsTrue $ Branch
  (Assignment [True, True])   -- (T ∨ (x₁ ∧ x₂))
  (Assignment [True, True])   -- (F ∨ (x₁ ∧ x₂))

-- p5 = ∀ y₁. ∀ y₂. ∃ x. ((y₁ ∨ y₂) ∧ x)
p5 = NotTrue

{-------------------------------------------------------------------------------

Problem 4
--------------

Finally, we now consider the embedding of the interesting bits of our language: the
quantifiers ∀ and ∃. You may be asking: but first, do we not need to consider
variables? The trick is: there are no variables! Or, perhaps it is more accurate
to say: we will shallow-embed QBF variables into Haskell Variables. The type
signature of the `forAll` and `exists` constructors reflects this: each take a
function of type

  (QBF -> QBF)

which represents the "body" of the formulae, and return a QBF. For example, the
formula

  ∀ x. ∃ y. (x ∧ y)

is represented in our embedding as

  forAll (\ x -> exists (\ y -> x `and` y))

Note that, as each QBF is itself a boolean, your definition of `forAll` and
`exists` should effectively "answer" the True Quantified Boolean Formulae
problem.

(see https://en.wikipedia.org/wiki/True_quantified_Boolean_formula).

That is, we should have that the following term

  forAll (\ x -> t `or` x)

evaluates to T, and that the following term

  forAll (\ x -> exists (\ y -> x `and` y))

evaluates to F. (Hence we say that our shallow embedding "eagerly evaluates"
formulae.)

Hint 1: Use the strategies you developed in Problem 3 to develop a general solution.
Hint 2: Your answer requires thought, but not necessarily a lot of code.


-------------------------------------------------------------------------------}


forAll , exists :: (QBF -> QBF) -> QBF


forAll phi = phi t `and` phi f
exists phi = phi t `or`  phi f

-- Here are the examples from above.
--
-- >>> forAll (\ x -> t `or` x)
-- True
-- >>> forAll (\ x -> exists (\ y -> x `and` y))
-- False

