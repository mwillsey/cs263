import LoVe.LoVelib
import AutograderLib
namespace LoVe
namespace BackwardProofs

/- # Homework 2: Backward Proofs

In this homework, you'll practice writing *backward* (or *tactical*) proofs.

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade. -/

section Q1_Simple_Proofs_Backwards
/- ## Question 1 (6 points): Backward Proofs

Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide.

Think about the similarity to the type inhabitation problems of HW1! -/

@[autogradedProof 1] theorem B (a b c : Prop) :
  (a → b) → (c → a) → c → b := by
  sorry

@[autogradedProof 1] theorem S (a b c : Prop) :
  (a → b → c) → (a → b) → a → c := by
  sorry

@[autogradedProof 1] theorem more_nonsense (a b c : Prop) :
  (c → (a → b) → a) → c → b → a := by
  sorry

@[autogradedProof 1]
theorem evenMoreNonsense (a b c: Prop):
  (a → b) → (c → a) → c → b := by
  sorry


@[autogradedProof 2]
theorem weak_peirce (a b : Prop) :
    ((((a → b) → a) → a) → b) → b := by
  sorry

end Q1_Simple_Proofs_Backwards





section Q2_Logical_Connectives
/- ## Question 2 (6 points): Logical Connectives

### 2.1 (1 point). Prove the following property about implication using basic
tactics.

Hints:

* Keep in mind that `¬ a` is defined as `a → False`. You can start by invoking
  `rw [Not]` or `unfold Not` if this helps you.

* You will need to apply the elimination rule for `∨`.

* You will need the elimination rule
  for `False` at some point in the proof.
  You may alternatively use the `contradiction` tactic:
  https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#contradiction
   -/

@[autogradedProof 1] theorem about_Impl (a b : Prop) :
  ¬ a ∨ b → a → b := by
  sorry


/- ### 2.2 (3 points).

The logical rules we have seen so far describe *intuitionistic* logic.
There are some statements that we can't prove using only these rules,
despite them perhaps "seeming" true.
(Food for thought: how could I argue that we *can't* prove certain propositions?)

Intuitionistic logic is extended to *classical* logic by assuming a classical
axiom, that allows us to prove these missing statements.
There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

We will prove the equivalence of these axioms: each one implies the others.

Hints:

* One way to find the definitions of `DoubleNegation` and `ExcludedMiddle`
  quickly is to

  1. hold down the Control (on Linux and Windows) or Command (on macOS) key;
  2. move the cursor to the identifier `DoubleNegation` or `ExcludedMiddle`;
  3. click the identifier.

* You can use `rw [DoubleNegation]` to unfold the definition of
  `DoubleNegation`, and similarly for the other definitions.

* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point. -/

#check DoubleNegation
#check ExcludedMiddle

@[autogradedProof 3, validAxioms #[Quot.sound, propext, funext]]
theorem EM_of_DN: DoubleNegation → ExcludedMiddle := by
  sorry

/- ### 2.3 (2 points).

The above homework question, together with the two implications from Exercise 3,
we have proved the following triangle of implications:
ExcludedMiddle → Peirce → DoubleNegation → ExcludedMiddle

Now let's show the reverse!
ExcludedMiddle → DoubleNegation → Peirce → ExcludedMiddle

Hint! these proofs are really easy, since we already have the theorems above.
my answers are one line each, no tactics

State and prove the three missing implications,
exploiting the three theorems we already have.
The three theorems you may use are `EM_of_DN` above, and
 two axioms I state below that are restatements of those from Ex3.
-/

axiom Peirce_of_EM : ExcludedMiddle → Peirce
axiom DN_of_Peirce : Peirce → DoubleNegation

-- enter your solution here

end Q2_Logical_Connectives

section Q3_Equality
/- ## Question 3 (2 points): Equality

You may hear it said that equality is the smallest *reflexive*, *symmetric*,
*transitive* relation. The following exercise shows that in the presence of
reflexivity, the rules for symmetry and transitivity are equivalent to a single
rule, "symmtrans". -/

axiom symmtrans {A : Type} {a b c : A} : a = b → c = b → a = c

-- You can now use `symmtrans` as a rule.

example (A : Type) (a b c : A) (h1 : a = b) (h2 : c = b) : a = c := by
  apply symmtrans
  apply h1
  apply h2

section

variable {A : Type}
variable {a b c : A}

/-! Replace the `sorry`s below with proofs, using `symmtrans` and `rfl`, without
using `Eq.symm`, `Eq.trans`, or `Eq.subst`. You should not use any tactics
besides `apply`, `exact`, and `rfl`.

Recall that you can `apply` a theorem supplied with some arguments,
 so if `x` is a hypothesis, then `apply symmtrans _ x` and `apply symmtrans x _`
 both might be valid.

My proofs are short, 2 tactics each.

-/

@[autogradedProof 1, validAxioms #[LoVe.BackwardProofs.symmtrans]]
theorem my_symm (h : b = a) : a = b := by
  sorry

@[autogradedProof 1, validAxioms #[LoVe.BackwardProofs.symmtrans]]
theorem my_trans (h1 : a = b) (h2 : b = c) : a = c := by
  sorry

end
end Q3_Equality


section Q4_Exists

/- ## Question 4: Existential Quantification (3 points)

We will need to build a little familiarity with Exists (∃)
 since we didn't cover it in detail before.

Like And and Or, there is nothing special about Exists.
It is simply an inductive type with one constructor, `Exists.intro`

Like And and Or, Exists takes some type parameters.
It takes a type `α` (implicitly bound) and a predicate `p : α → Prop` (explicitly bound).


See more info in the "Theorem Proving in Lean" book:
https://lean-lang.org/theorem_proving_in_lean4/Quantifiers-and-Equality/#the-existential-quantifier
-/

#print And
#print Exists


-- if we supply a predicate (a function to Prop) to Exists, we get a new Prop
#check Exists (fun a : ℕ => a > 5)
-- this is sugar for the above
#check ∃a : ℕ, a > 5


-- To prove a proposition of the form `∃a : α, p a`, we can use the constructor `Exists.intro`
#check Exists.intro

-- example is just a nameless theorem
example : ∃a : ℕ, a = 2 + 2 :=
  -- first argument is the witness, the thing that exists to satisfy the predicate
  -- second argument is the proof that the witness actually satisfies the predicate
  Exists.intro 4 (Eq.refl 4)

-- tactics work too
example : ∃a : ℕ, a = 2 + 2 := by
  -- typically you want to apply Exists.intro with the witness as an argument
  -- since that's the thing you have to come up with
  apply Exists.intro 4
  rfl


/-
How to use an existential hypothesis? We can use the elimination rule for Exists, `Exists.elim`.
This takes:
1. an existential hypothesis, i.e., a proof of `∃a : α, p a`;
2. a function that shows how to proof some `b` given an arbitrary witness `a` and a proof that `p a` holds.
and gives us a proof of `b`.
-/

#check Exists.elim


example (a: ℕ) (h: ∃b, a = b + 1): ¬a = 0 := by
  intro b0
  -- eliminating the existential hypothesis `h`
  --  doesn't give us a witness, but gives us a way to prove the goal
  -- if we can show it from any witness that satisfies the predicate
  apply Exists.elim h
  intro b' h_eq
  -- `rw .. at` allows you to rewrite at a specific hypothesis, rather than the goal
  rw [b0] at h_eq
  -- the `contradiction` tactic proves any goal if the hypotheses contain a
  -- contradiction. In this case, we have `0 = b' + 1`,
  -- since a Nat must be either 0 or a successor.
  contradiction


/-
Now prove the following theorem.

My proof is about 5ish tactics for each direction,
 and uses `Exists.intro` in the forward direction and `Exists.elim` in the backward direction.
-/
@[autogradedProof 3]
theorem exists_forall {α : Type} (p: α → Prop):
  ¬(∃x : α, p x) ↔ ∀y : α, ¬ p y := by
  sorry

end Q4_Exists


section Q5_Pythagorean_Triples

/- ## Question 4 (3 points): Pythagorean Triples

A Pythagorean triple is a "triple" of three natural numbers `a`,
`b`, and `c` such that `a² + b² = c²`, i.e., they are integer sides of a right
triangle. -/

def IsPythagoreanTriple (a b c : ℕ) : Prop :=
  a^2 + b^2 = c^2

/-! By assuming Fermat's Last Theorem
(https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem), we can show that if
`a`, `b`, and `c` form a Pythagorean triple, then `a`, `b`, and `c` can't all be
perfect squares. Use the definitions below to prove this. -/

axiom fermats_last_theorem (x y n : ℕ) :
  (n ≥ 3) → ¬∃ (z : ℕ), x^n + y^n = z^n

def IsSquare (n : ℕ) : Prop := ∃ (u : ℕ), n = u^2

-- **Note**: You may use the following lemma in your proof.
lemma square_square (a b c : ℕ) :
  (a^2)^2 + (b^2)^2 = (c^2)^2 → a^4 + b^4 = c^4 :=
by intro h; rw [←pow_mul, ←pow_mul, ←pow_mul] at h; exact h

/-! Hints:
* `And.elim` behaves a bit weirdly. If you want to extract proofs of `P` and `Q`
  from a proof of a conjunction `h : P ∧ Q`, use `h.left` and `h.right` rather than
  `And.elim h`.
* Remember that `have p := ...` allows you do some forward reasoning,
   giving you a new hypothesis `p` that you can use in the rest of the proof.
* If you have a hypothesis `h : a = b` and want to replace `b` with `a` in your
  goal (instead of `a` with `b`), use `rw [←h]` (note the `←`).
* You can use `rw [stuff] at h` to rewrite in a hypothesis rather than the goal.
* You can use the `decide` tactic to prove that `4 ≥ 3`.


My proof does some unfolding,
 then a bunch of intro and elims to unpack the `And`s and `Exists`s,
When I apply `fermats_last_theorem`, I supply arguments for all of its
 parameters `x`, `y`, and `n`, and then use `decide` to prove the side condition `n ≥ 3`.


Note: You may not use `simp` in your solution. (If you need to expand a
definition, you can use `rw`.) -/

@[autogradedProof 3,
  validAxioms #[LoVe.BackwardProofs.fermats_last_theorem, Quot.sound, propext, funext, Classical.choice]]
theorem pythagorean_triple_not_all_squares (a b c : ℕ) :
  IsPythagoreanTriple a b c → ¬(IsSquare a ∧ IsSquare b ∧ IsSquare c) := by
  sorry


end Q5_Pythagorean_Triples


section Q6_List_Functions

/- ## Question 6: List Functions (6 points)
In the previous homework, you stated some theorems about
   snoc, sum, and reverse. Let's prove those theorems now. -/

def snoc {α : Type} : List α → α → List α
  | [],      n => [n]
  | m :: ms, n => m :: snoc ms n

def reverse {α : Type} : List α → List α
  | []      => []
  | m :: ms => snoc (reverse ms) m

def sum : List ℕ → ℕ
  | []      => 0
  | m :: ms => m + sum ms

-- hint: you may want `ac_rfl` in the induction case
@[autogradedProof 2]
theorem sum_snoc (ms : List ℕ) (n : ℕ) :
  sum (snoc ms n) = n + sum ms := by
  sorry

-- you may want to check out the definition of `List.append` in the Lean library
-- to figure out what to induct on
#check List.append

@[autogradedProof 2]
theorem sum_append (ms ns : List ℕ) :
  sum (ms ++ ns) = sum ms + sum ns := by
  sorry

@[autogradedProof 2]
-- hint: use a theorem that you proved earlier in this homework
theorem sum_reverse (ns : List ℕ) :
  sum (reverse ns) = sum ns := by
  sorry

end Q6_List_Functions

end BackwardProofs
end LoVe
