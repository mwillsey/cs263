/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import AutograderLib
import LoVe.LoVelib


/- # LoVe Homework 1 (20 points): Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (6 points): Type Inhabitation

We start by declaring four new opaque types. -/

opaque α : Type
opaque β : Type
opaque γ : Type
opaque δ : Type

/- (4 points). Complete the following definitions, by providing terms with
the expected type.

Please use reasonable names for the bound variables, e.g., `a : α`, `b : β`,
`c : γ`.

Hint: A procedure for doing so systematically is described in Section 1.4 of the
Hitchhiker's Guide. As explained there, you can use `_` as a placeholder while
constructing a term. By hovering over `_`, you will see the current logical
context. -/

@[autogradedDef 1]
def B : (α → β) → (γ → α) → γ → β :=
  sorry

@[autogradedDef 1]
def S : (α → β → γ) → (α → β) → α → γ :=
  sorry

@[autogradedDef 1]
def moreNonsense : ((α → β) → γ → δ) → γ → β → δ :=
  sorry

@[autogradedDef 1]
def evenMoreNonsense : (α → β) → (α → γ) → α → β → γ :=
  sorry


/- (2 points). Complete the following definition.

This one looks more difficult, but it should be fairly straightforward if you
follow the procedure described in the Hitchhiker's Guide.

Hint: You might have to call the same function multiple time.
  It might feel circular, but you'll have different things
  available to you in the different contexts.

Note: Peirce is pronounced like the English word "purse". -/

@[autogradedDef 2]
def weakPeirce : ((((α → β) → α) → α) → β) → β :=
  sorry


/- ## Question 2 (4 points): Snoc

(3 points). Define the function `snoc` that appends a single element to the
end of a list. Your function should be defined by recursion and not using `++`
(`List.append`). -/

@[autogradedDef 3]
def snoc {α : Type} (xs: List α) (x : α) : List α :=
  sorry

/- (1 point). Convince yourself that your definition of `snoc` works by
testing it on at least 2 more examples. -/

#eval snoc [1] 2 -- expected: [1, 2]
-- invoke `#eval` here, include a comment showing the expected result


/- ## Question 3 (6 points): Sum

(3 points). Define a `sum` function that computes the sum of all the numbers
in a list. -/

@[autogradedDef 3]
def sum (xs: List ℕ):  ℕ :=
  sorry

#eval sum [1, 12, 3]   -- expected: 16

/- (3 points). State (without proving them) the following properties of
`sum` as theorems. Schematically:

     sum (snoc ms n) = n + sum ms
     sum (ms ++ ns) = sum ms + sum ns
     sum (reverse ns) = sum ns

Try to give meaningful names to your theorems. Use `sorry` as the proof. -/

-- enter your theorem statements here

/- ## Question 4 (4 points): Typing Derivation

Show the typing derivation for your definition of `B` above, using ASCII or
Unicode art. Start with an empty context. You might find the characters `–` (to
draw horizontal bars) and `⊢` useful.

Feel free to introduce abbreviations to avoid repeating large contexts `C`. -/

-- write your solution here

end LoVe
