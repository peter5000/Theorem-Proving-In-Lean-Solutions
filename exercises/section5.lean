/-!
    Theorem Proving in Lean 4, Section 5
    Tactics
    https://lean-lang.org/theorem_proving_in_lean4/tactics.html
-/

-- Turn off unused variables linter, since some problem statements have
-- unused variables.
set_option linter.unusedVariables false

-- Problem 1. Go back to the exercises in Chapter Propositions and Proofs and Chapter Quantifiers and Equality and redo as many as you can now with tactic proofs, using also `rw` and `simp` as appropriate.

-- Propositions and Proofs --
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by sorry
example : p ∨ q ↔ q ∨ p := by sorry

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by sorry

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := by sorry
example : ¬(p ∧ ¬p) := by sorry
example : p ∧ ¬q → ¬(p → q) := by sorry
example : ¬p → (p → q) := by sorry
example : (¬p ∨ q) → (p → q) := by sorry
example : p ∨ False ↔ p := by sorry
example : p ∧ False ↔ False := by sorry

example : (p → q) → (¬q → ¬p) := by sorry

open Classical
variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := by sorry
example : ¬(p → q) → p ∧ ¬q := by sorry
example : (p → q) → (¬p ∨ q) := by sorry
example : (¬q → ¬p) → (p → q) := by sorry
example : p ∨ ¬p := by sorry
example : (((p → q) → p) → p) := by sorry

-- Prove the following statement without using classical logic
example : ¬(p ↔ ¬p) := by sorry

-- Quantifiers and Equality --

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by sorry

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by sorry

open Classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by sorry

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by sorry

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by sorry

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by sorry
example (a : α) : r → (∃ x : α, r) := by sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by sorry

-- Problem 2: Use tactic combinators to obtain a one line proof of the following.
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by sorry
