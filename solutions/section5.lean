-- Theorem Proving in Lean 4, Section 5
-- Tactics
-- https://lean-lang.org/theorem_proving_in_lean4/tactics.html

-- 1
-- Propositions and Proofs
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro h
    constructor
    . exact h.right
    . exact h.left
  . intro h
    constructor
    . exact h.right
    . exact h.left

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    . intro hp
      apply Or.inr
      assumption
    . intro hq
      apply Or.inl
      assumption
  . intro h
    apply Or.elim h
    . intro hp
      apply Or.inr
      assumption
    . intro hq
      apply Or.inl
      assumption

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro h
    constructor
    exact h.left.left
    constructor
    exact h.left.right
    exact h.right
  . intro h
    repeat constructor
    exact h.left
    exact h.right.left
    exact h.right.right

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | inl hp => apply Or.inl; assumption
      | inr hq => apply Or.inr; apply Or.inl; assumption
    | inr hr => apply Or.inr; apply Or.inr; assumption
  . intro h
    cases h with
    | inl hp => apply Or.inl; apply Or.inl; assumption
    | inr hqr =>
      cases hqr with
      | inl hq => apply Or.inl; apply Or.inr; assumption
      | inr hr => apply Or.inr; assumption

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hp => exact ⟨Or.inl hp, Or.inl hp⟩
    | inr hqr => exact ⟨Or.inr hqr.left, Or.inr hqr.right⟩
  . intro h
    cases h.left with
    | inl hp => exact Or.inl hp
    | inr hq =>
      cases h.right with
      | inl hp2 => exact Or.inl hp2
      | inr hr => exact Or.inr ⟨hq, hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intros h hpq
    exact h hpq.left hpq.right
  . intros h hp hq
    exact h ⟨hp, hq⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    constructor
    . intro hp
      exact h (Or.inl hp)
    . intro hq
      exact h (Or.inr hq)
  . intros h hpq
    cases hpq with
    | inl hp => exact h.left hp
    | inr hq => exact h.right hq

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  simp

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  simp
  intros h hp
  cases h with
  | inl hnp => exact absurd hp hnp
  | inr hnq => exact hnq

example : ¬(p ∧ ¬p) := by
  simp

example : p ∧ ¬q → ¬(p → q) := by
  simp

example : ¬p → (p → q) := by
  intros h hp
  exact absurd hp h

example : (¬p ∨ q) → (p → q) := by
  intros h hp
  cases h with
  | inl hnp => exact absurd hp hnp
  | inr hq => exact hq

example : p ∨ False ↔ p := by
  simp

example : p ∧ False ↔ False := by
  simp

example : (p → q) → (¬q → ¬p) := by
  intros h hnq hp
  exact hnq (h hp)

open Classical
variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  cases (em p) with
  | inl hp =>
    cases (h hp) with
    | inl hq => apply Or.inl; intro _; assumption
    | inr hr => apply Or.inr; intro _; assumption
  | inr hnp => apply Or.inl; intro hp; exact absurd hp hnp

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  cases (em p) with
  | inl hp =>
    apply Or.inr
    intro hq
    exact h ⟨hp, hq⟩
  | inr hnp =>
    exact Or.inl hnp

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  cases (em p) with
  | inl hp =>
    cases (em q) with
    | inl hq => apply absurd (by intro _; assumption) h
    | inr hnq => exact ⟨hp, hnq⟩
  | inr hnp => exact absurd (by intro hp; exact absurd hp hnp) h

example : (p → q) → (¬p ∨ q) := by
  intro h
  cases (em p) with
  | inl hp => exact Or.inr (h hp)
  | inr hnp => exact Or.inl hnp

example : (¬q → ¬p) → (p → q) := by
  intros h hp
  cases (em q) with
  | inl hq => assumption
  | inr hnq => exact absurd hp (h hnq)

example : p ∨ ¬p := by
  exact em p

example : (((p → q) → p) → p) := by
  intro h
  cases (em p) with
  | inl hp => exact hp
  | inr hnp => exact h (by intro hp; exact absurd hp hnp)

-- Prove following statement without using classical logic
example : ¬(p ↔ ¬p) := by
  intro h
  let hnp : ¬p := (by intro hp; exact h.mp hp hp)
  exact hnp (h.mpr hnp)

------------------------------------------------------------------

-- Quantifiers and Equality

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h
    constructor <;> intro x <;> (first | exact (h x).left | exact (h x).right)
  . intros h x
    constructor <;> (first | exact h.left x | exact h.right x)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intros h hpx x
  exact h x (hpx x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intros h x
  cases h with
  | inl hpx => exact Or.inl (hpx x)
  | inr hqx => exact Or.inr (hqx x)

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro α
  apply Iff.intro
  . intro h
    exact h α
  . intro h _
    exact h

open Classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  . intro h
    cases (em r) with
    | inl hr => exact Or.inr hr
    | inr hnr =>
      apply Or.inl
      intro x
      cases (h x) with
      | inl hpx => exact hpx
      | inr hr => exact absurd hr hnr
  . intros h x
    cases h with
    | inl hpx => exact Or.inl (hpx x)
    | inr hr => exact Or.inr hr

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  . intros h hr x
    exact h x hr
  . intros h x hr
    exact h hr x

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  apply (h barber).mp
    ((h barber).mpr
      (by intro hsbb; exact (h barber).mp hsbb hsbb))
  exact ((h barber).mpr
      (by intro hsbb; exact (h barber).mp hsbb hsbb))

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  simp

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  exact ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  simp[Iff.intro]

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  . intro ⟨x, h⟩
    cases h with
    | inl hpx => exact Or.inl ⟨x, hpx⟩
    | inr hqx => exact Or.inr ⟨x, hqx⟩
  . intro h
    cases h with
    | inl hxpx => have ⟨x, hpx⟩ := hxpx; exact ⟨x, Or.inl hpx⟩
    | inr hxqx => have ⟨x, hqx⟩ := hxqx; exact ⟨x, Or.inr hqx⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  simp

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  simp

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  simp

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  simp

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  simp

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  . intro ⟨x, hpxr⟩ hxpx
    exact hpxr (hxpx x)
  . intro h
    cases (em (∀ x, p x)) with
    | inl hxpx => exact ⟨a, (by intro _; exact h hxpx)⟩
    | inr hnxpx =>
      cases (em (∃ x, p x → r)) with
      | inl hxpxr => exact hxpxr
      | inr hnxpxr => exact absurd (by intro x; cases (em (p x)) with | inl hpx => exact hpx | inr hnpx => exact absurd ⟨x, (by intro hp; exact absurd hp hnpx)⟩ hnxpxr) hnxpx

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  . intro ⟨x, hrpx⟩ hr
    exact ⟨x, hrpx hr⟩
  . intro h
    cases (em r) with
    | inl hr => have ⟨a, hpx⟩ := h hr; exact ⟨a, (by intro _; assumption)⟩
    | inr hnr => exact ⟨a, (by intro hr; exact absurd hr hnr)⟩

-- 2
-- One line proof using tactic combinators
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat constructor <;> repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
