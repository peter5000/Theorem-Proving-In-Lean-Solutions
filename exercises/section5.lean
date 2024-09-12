-- Theorem Proving in Lean 4, Section 5
-- Tactics
-- https://lean-lang.org/theorem_proving_in_lean4/tactics.html

-- 1
-- Propositions and Proofs
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by admit
example : p ∨ q ↔ q ∨ p := by admit

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by admit

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by admit

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by admit
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by admit

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by admit
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by admit
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by admit
example : ¬p ∨ ¬q → ¬(p ∧ q) := by admit
example : ¬(p ∧ ¬p) := by admit
example : p ∧ ¬q → ¬(p → q) := by admit
example : ¬p → (p → q) := by admit
example : (¬p ∨ q) → (p → q) := by admit
example : p ∨ False ↔ p := by admit
example : p ∧ False ↔ False := by admit

example : (p → q) → (¬q → ¬p) := by admit

open Classical
variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by admit
example : ¬(p ∧ q) → ¬p ∨ ¬q := by admit
example : ¬(p → q) → p ∧ ¬q := by admit
example : (p → q) → (¬p ∨ q) := by admit
example : (¬q → ¬p) → (p → q) := by admit
example : p ∨ ¬p := by admit
example : (((p → q) → p) → p) := by admit

-- Prove following statement without using classical logic
example : ¬(p ↔ ¬p) := by admit

------------------------------------------------------------------

-- Quantifiers and Equality

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by admit
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by admit
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by admit

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by admit

open Classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by admit

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by admit

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by admit

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by admit
example (a : α) : r → (∃ x : α, r) := by admit
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by admit
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by admit

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by admit
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by admit
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by admit
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by admit
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by admit

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by admit
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by admit
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by admit

-- 2
-- One line proof using tactic combinators
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by admit
