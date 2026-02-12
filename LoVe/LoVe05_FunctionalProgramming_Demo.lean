/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Demo 5: Functional Programming

We take a closer look at the basics of typed functional programming: inductive
types, proofs by induction, recursive functions, pattern matching, structures
(records), and type classes. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Inductive Types

Recall the definition of type `Nat`: -/

#print Nat

/- Mottos:

* **No junk**: The type contains no values beyond those expressible using the
  constructors.

* **No confusion**: Values built in a different ways are different.

For `Nat`:

* "No junk" means that there are no special values, say, `–1` or `ε`, that
  cannot be expressed using a finite combination of `Nat.zero` and `Nat.succ`.

* "No confusion" is what ensures that `Nat.zero` ≠ `Nat.succ n`.

In addition, values of inductive types are always finite.
`Nat.succ (Nat.succ …)` is not a value.


## Structural Induction

__Structural induction__ is a generalization of mathematical induction to
inductive types. To prove a property `P[n]` for all natural numbers `n`, it
suffices to prove the base case

    `P[0]`

and the induction step

    `∀k, P[k] → P[k + 1]`

For lists, the base case is

    `P[[]]`

and the induction step is

    `∀y ys, P[ys] → P[y :: ys]`

In general, there is one subgoal per constructor, and induction hypotheses are
available for all constructor arguments of the type we are doing the induction
on. -/

theorem Nat.succ_neq_self (n : ℕ) :
    Nat.succ n ≠ n :=
  by
    induction n with
    | zero       => simp
    | succ n' ih => simp [ih]


/- ## Structural Recursion

__Structural recursion__ is a form of recursion that allows us to peel off
one constructor from the value on which we recurse. Such functions are
guaranteed to call themselves only finitely many times before the recursion
stops. This is a prerequisite for establishing that the function terminates. -/

def fact : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fact n

def factThreeCases : ℕ → ℕ
  | 0     => 1
  | 1     => 1
  | n + 1 => (n + 1) * factThreeCases n

/- For structurally recursive functions, Lean can automatically prove
termination. For more general recursive schemes, the termination check may fail.
Sometimes it does so for a good reason, as in the following example: -/

/-
-- fails
def illegal : ℕ → ℕ
  | n => illegal n + 1
-/

opaque immoral : ℕ → ℕ

axiom immoral_eq (n : ℕ) :
    immoral n = immoral n + 1

theorem proof_of_False :
    False :=
  have hi : immoral 0 = immoral 0 + 1 :=
    immoral_eq 0
  have him :
    immoral 0 - immoral 0 = immoral 0 + 1 - immoral 0 :=
    by rw [←hi]
  have h0eq1 : 0 = 1 :=
    by simp at him
  show False from
    by simp at h0eq1


/- ## Pattern Matching Expressions

    `match` _term₁_, …, _termM_ `with`
    | _pattern₁₁_, …, _pattern₁M_ => _result₁_
        ⋮
    | _patternN₁_, …, _patternNM_ => _resultN_

`match` allows nonrecursive pattern matching within terms. -/

def bcount {α : Type} (p : α → Bool) : List α → ℕ
  | []      => 0
  | x :: xs =>
    match p x with
    | true  => bcount p xs + 1
    | false => bcount p xs

def min (a b : ℕ) : ℕ :=
  if a ≤ b then a else b

/- ## Aside on `Bool` vs `Prop` -/

/- `Bool` is a type with two values, `true` and `false`.
   We will prefer it for computation -/
#print Bool
#check (true: Bool)
#check (false: Bool)
#check 1 == 1
#check 1 == 0

/- Prop is the type of logical propositions. We will prefer it for reasoning.

  Each proposition may have 0 or more "proofs" (i.e., terms of that type).
  For example, the proposition `1 = 1` has a proof, `Eq.refl 1`,
   while the proposition `1 = 0` has no proofs.
  We do not (cannot!) distinguish between different proofs of the same proposition.
 -/

#check Prop
#check (True: Prop)
#check (False: Prop)
#check 1 = 1
#check Eq.refl 1
#check 1 = 0
#check (1 = 1) ∧ (2 = 2)

-- watch out, Lean will convert from `Prop` to `Bool`
#check Bool.and
#check Bool.and (1 = 1) (2 = 2)
#check Bool.and False True
#check decide


/- ## Structures

Lean provides a convenient syntax for defining records, or structures. These are
essentially nonrecursive, single-constructor inductive types. -/

structure RGB where
  red   : ℕ
  green : ℕ
  blue  : ℕ

#check RGB.mk
#check RGB.red
#check RGB.green
#check RGB.blue

namespace RGB_as_inductive

/- The RGB structure definition is equivalent to the following set of
definitions: -/

inductive RGB : Type where
  | mk : ℕ → ℕ → ℕ → RGB

def RGB.red : RGB → ℕ
  | RGB.mk r _ _ => r

def RGB.green : RGB → ℕ
  | RGB.mk _ g _ => g

def RGB.blue : RGB → ℕ
  | RGB.mk _ _ b => b

end RGB_as_inductive

/- A new structure can be created by extending an existing structure: -/

structure RGBA extends RGB where
  alpha : ℕ

/- An `RGBA` is a `RGB` with the extra field `alpha : ℕ`. -/

#print RGBA

def pureRed : RGB :=
  RGB.mk 0xff 0x00 0x00

def pureGreen : RGB :=
  { red   := 0x00
    green := 0xff
    blue  := 0x00 }

def semitransparentGreen : RGBA :=
  { pureGreen with
    alpha := 0x7f }

#print pureRed
#print pureGreen
#print semitransparentGreen

def shuffle (c : RGB) : RGB :=
  { red   := RGB.green c
    green := RGB.blue c
    blue  := RGB.red c }

/- Alternative definition using pattern matching: -/

def shufflePattern : RGB → RGB
  | RGB.mk r g b => RGB.mk g b r

theorem shuffle_shuffle_shuffle (c : RGB) :
    shuffle (shuffle (shuffle c)) = c :=
  by rfl


/- ### **Dot notation**

When you type `x.f`, Lean expands this to `($TypeOfX.f x)`.
As we see above, "fields" of structures are sort of a fiction,
 instead, they are just functions that take the whole structure as an argument and
 project out the relevant part.
We've also seen various ways in which you can just say `.f` have Lean figure out
 exactly which method you meant.

When you define a type, Lean also defines a namespace of the same name.
Constructors and projection functions are defined in that namespace.

You can define your own functions in that namespace, and they will also be available in dot notation.
-/

def shuffleDot   (c: RGB): RGB := RGB.mk c.green c.blue c.red
def shuffleDot2  (c: RGB): RGB :=    .mk c.green c.blue c.red

-- `⟨a,b,c⟩` is the *anonymous constructor* syntax sugar for `.mk a b c`
-- https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#anonymous-constructor-syntax
#guard (1, 2) = ⟨1, 2⟩
#guard And.intro True.intro True.intro = ⟨⟨⟩, ⟨⟩⟩
#check (⟨1, 2, 3⟩ : RGB)

def shuffleAngle (c: RGB): RGB := ⟨c.green, c.blue, c.red⟩

-- we can define shuffle in the RGB namespace, and then we can use dot notation to call it
def RGB.shuffle (c: RGB): RGB := ⟨c.green, c.blue, c.red⟩
#guard pureRed.shuffle.blue = 0xff

/- ## Type Classes

A __type class__ is a structure type combining abstract constants and their
properties. A type can be declared an instance of a type class by providing
concrete definitions for the constants and proving that the properties hold.
Based on the type, Lean retrieves the relevant instance. -/

#print Inhabited

class MyInhabited (α : Type) where
  default : α

instance Nat.Inhabited : Inhabited ℕ :=
  { default := 0 }

instance List.Inhabited {α : Type} : Inhabited (List α) :=
  { default := [] }

#eval (Inhabited.default : ℕ)
#eval (Inhabited.default : List Int)

-- New kind of binder!!
def head {α : Type} [Inhabited α] : List α → α
  | []     => Inhabited.default
  | x :: _ => x

theorem head_head {α : Type} [Inhabited α] (xs : List α) :
    head [head xs] = head xs :=
  by rfl

#guard head [] = 0

-- Lean's List.head is slighty different
#check List.head
-- Lean's `List.head!` does rely on `Inhabited`, and it panics if the list is empty?
-- panic relies on `Inhabited` to supply a dummy value
#check List.head!

instance Fun.Inhabited {α β : Type} [Inhabited β] :
  Inhabited (α → β) :=
  { default := fun _ ↦ Inhabited.default }

instance Prod.Inhabited {α β : Type}
    [Inhabited α] [Inhabited β] :
  Inhabited (α × β) :=
  { default := (Inhabited.default, Inhabited.default) }

/- Aside from inhabited, there many other type classes
   that only have a single constant -/

#print Add
#print Mul
#print Zero
#print One

-- #synth will find the instance of `Add Nat`
#synth Add Nat

/- We encountered these type classes in lecture 3:
   Note how these are parameterized by an operation,
   and the field of the type class is a property of that operation.
-/

#print Std.Associative
#print Std.Commutative


/- We will make use of more complex typeclasses as we move on in class -/


/- ## Lists

`List` is an inductive polymorphic type constructed from `List.nil` and
`List.cons`: -/

#print List

/- `cases` performs a case distinction on the specified term. This gives rise
to as many subgoals as there are constructors in the definition of the term's
type. The tactic behaves the same as `induction` except that it does not
produce induction hypotheses. Here is a contrived example: -/

theorem head_head_cases {α : Type} [Inhabited α]
      (xs : List α) :
    head [head xs] = head xs :=
  by
    -- cases xs with
    -- | nil        => rfl
    -- | cons x xs' => rfl
    cases xs
    . rfl
    . rfl

/- `match` is the structured equivalent: -/

theorem head_head_match {α : Type} [Inhabited α]
      (xs : List α) :
    head [head xs] = head xs :=
  match xs with
  | List.nil        => by rfl
  | List.cons x xs' => by rfl

/- `cases` works on any inductive type!
Here we use it on a hypothesis of the form `l = r`. It matches `r`
against `l` and replaces all occurrences of the variables occurring in `r` with
the corresponding terms in `l` everywhere in the goal. -/

theorem injection_example {α : Type} (x y : α) (xs ys : List α)
      (h : x :: xs = y :: ys) :
    x = y ∧ xs = ys :=
  by
    -- how can `x :: xs = y :: ys` be true?
    -- it must be that `x = y` and `xs = ys`.
    cases h
    simp

/- If `r` fails to match `l`, no subgoals emerge; the proof is complete. -/

theorem distinctness_example {α : Type} (y : α) (ys : List α)
      (h : [] = y :: ys) :
    False :=
  by cases h

-- More list functions

def map {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: map f xs

def mapArgs {α β : Type} : (α → β) → List α → List β
  | _, []      => []
  | f, x :: xs => f x :: mapArgs f xs

-- Lean's List already has this, ours is the same!
#check List.map
theorem map_eq_list_map {α β: Type} (f: α → β) (xs: List α):
    map f xs = List.map f xs :=
  by
    induction xs with
    | nil           => rfl
    | cons x xs' ih => simp [map, List.map, ih]

theorem map_ident {α : Type} (xs : List α) :
    map (fun x ↦ x) xs = xs :=
  by
    induction xs with
    | nil           => rfl
    | cons x xs' ih => simp [map, ih]

theorem map_comp {α β γ : Type} (f : α → β) (g : β → γ)
      (xs : List α) :

    -- map g (map f xs) = map (fun x ↦ g (f x)) xs :=
    map g (map f xs) = map (g ∘ f) xs :=
  by
    induction xs with
    | nil           => rfl
    | cons x xs' ih => simp [map, ih]

theorem map_append {α β : Type} (f : α → β)
      (xs ys : List α) :
    map f (xs ++ ys) = map f xs ++ map f ys :=
  by
    induction xs with
    | nil           => rfl
    | cons x xs' ih => simp [map, ih]

-- Notice how similar all those proofs are! That is typical.


-- more list functions
-- tail is easy to make total
def tail {α : Type} : List α → List α
  | []      => []
  | _ :: xs => xs

-- we saw how to make `head` with `Inhabited` but here is a version that uses `Option`
def headOpt {α : Type} : List α → Option α
  | []     => Option.none
  | x :: _ => Option.some x

#check List.head? -- Lean's version of this


-- yet another version, force the user to provide a proof that the list is not empty
def headPre {α : Type} : (xs : List α) → xs ≠ [] → α
  | [],     hxs => by contradiction
  | x :: _, hxs => x

#check List.head -- Lean's version of this

#eval headOpt [3, 1, 4]
#eval headPre [3, 1, 4] (by simp) -- using tactics in parens!

def zip {α β : Type} : List α → List β → List (α × β)
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  | [],      _       => []
  | _ :: _,  []      => []

#check List.zip

def length {α : Type} : List α → ℕ
  | []      => 0
  | x :: xs => length xs + 1

#check List.length

/- `cases` can also be used to perform a case distinction on a proposition, in
conjunction with `Classical.em`. Two cases emerge: one in which the proposition
is true and one in which it is false. -/

#check Classical.em

theorem min_add_add (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  by
    have h := Classical.em (m ≤ n)
    cases h with
    | inl h => simp [min, h]
    | inr h => simp [min, h]

theorem min_add_add_match (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  match Classical.em (m ≤ n) with
  | Or.inl h => by simp [min, h]
  | Or.inr h => by simp [min, h]

theorem min_add_add_if (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  -- new syntax!
  -- this gives us `h` in the true branch and `¬h` in the false branch
  if h : m ≤ n then
    by simp [min, h]
  else
    by simp [min, h]

theorem length_zip {α β : Type} (xs : List α) (ys : List β) :
    length (zip xs ys) = min (length xs) (length ys) :=
  by
    -- uh oh, we want to do induction on xs, but ys is already fixed!
    -- induction xs with -- this fails, try it
    induction xs generalizing ys with
    | nil           => simp [zip, length, min]
    | cons x xs' ih =>
      cases ys with
      | nil        => rfl
      | cons y ys' => simp [zip, length, ih ys', min_add_add]

theorem map_zip {α α' β β' : Type} (f : α → α')
      (g : β → β') :
    ∀xs ys,
      map (fun ab : α × β ↦
          (f (Prod.fst ab), g (Prod.snd ab)))
        (zip xs ys) =
      zip (map f xs) (map g ys)
  -- note how these patterns are the same as those in `zip`!
  -- this is good style, makes the proof easier
  | x :: xs, y :: ys => by simp [zip, map, map_zip f g xs ys]
  | [],      _       => by rfl
  | _ :: _,  []      => by rfl
  -- could do similar for length_zip


/- ## Binary Trees

Inductive types with constructors taking several recursive arguments define
tree-like objects. __Binary trees__ have nodes with at most two children. -/

#print Tree

#check Tree.node 1 (.node 2 .nil .nil) .nil

/- The type `AExp` of arithmetic expressions was also an example of a tree data
structure.

The nodes of a tree, whether inner nodes or leaf nodes, often carry labels or
other annotations.

Inductive trees contain no infinite branches, not even cycles. This is less
expressive than pointer- or reference-based data structures (in imperative
languages) but easier to reason about.

Recursive definitions (and proofs by induction) work roughly as for lists, but
we may need to recurse (or invoke the induction hypothesis) on several child
nodes. -/

def mirror {α : Type} : Tree α → Tree α
  | Tree.nil        => Tree.nil
  | Tree.node a l r => Tree.node a (mirror r) (mirror l)

theorem mirror_mirror {α : Type} (t : Tree α) :
    mirror (mirror t) = t :=
  by
    induction t with
    | nil                  => rfl
    -- we get 2 ih's!
    | node a l r ih_l ih_r => simp [mirror, ih_l, ih_r]

-- same proof, done using calc
-- we will manually recursively call the theorem, instead of using the induction hypothesis
theorem mirror_mirror_calc {α : Type} :
    ∀t : Tree α, mirror (mirror t) = t
  | Tree.nil        => by rfl
  | Tree.node a l r =>
    calc
      mirror (mirror (Tree.node a l r))
      = mirror (Tree.node a (mirror r) (mirror l)) :=
        by rfl
      _ = Tree.node a (mirror (mirror l))
        (mirror (mirror r)) :=
        by rfl
      _ = Tree.node a l (mirror (mirror r)) :=
        by rw [mirror_mirror_calc l]
      _ = Tree.node a l r :=
        by rw [mirror_mirror_calc r]

theorem mirror_Eq_nil_Iff {α : Type} :
    ∀t : Tree α, mirror t = Tree.nil ↔ t = Tree.nil
  | Tree.nil        => by simp [mirror]
  | Tree.node _ _ _ => by simp [mirror]
  -- := by intros
  --       cases t
  --       . simp [mirror]
  --       . simp [mirror]


/- ## Dependent Inductive Types -/

inductive Vec (α : Type) : ℕ → Type where
  | nil                                : Vec α 0
  | cons (a : α) {n : ℕ} (v : Vec α n) : Vec α (n + 1)

#check Vec.nil
#check Vec.cons

def vec134 := Vec.cons 3 (Vec.cons 1 (Vec.cons 4 Vec.nil))
#check vec134
#check (vec134: Vec ℕ 3)
#check (vec134: Vec ℕ (2 + 1))
#check (vec134: Vec ℕ (if 1 + 1 = 2 then 3 else 4))

def listOfVec {α : Type} {n : ℕ} : Vec α n → List α
  | Vec.nil      => []
  | Vec.cons a v => a :: listOfVec v

def vecOfList {α : Type} : (xs : List α) → Vec α (List.length xs)
  | []      => Vec.nil
  | x :: xs => Vec.cons x (vecOfList xs)
  -- I produced things of "different types" in each arm!

-- simplest example
def sillyproof (n: ℕ): n = n :=
  -- Eq.refl n
  match n with
  | 0 => Eq.refl 0
  | Nat.succ m => Eq.refl m.succ

-- what match actually desugars to!
#check Nat.rec

theorem length_listOfVec {α : Type} (n : ℕ) (v : Vec α n):
  List.length (listOfVec v) = n :=

  -- match v with
  -- | Vec.nil      => by rfl
  -- | Vec.cons a v2 => by simp [listOfVec, length_listOfVec _ v2]

  -- match n, v with
  -- | 0, Vec.nil      => by rfl
  -- | m+1, Vec.cons a v2 => by simp [listOfVec, length_listOfVec _ v2]

  by
    induction v
    . rfl
    . simp [listOfVec, v_ih]

end LoVe
