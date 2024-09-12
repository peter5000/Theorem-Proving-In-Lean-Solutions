/-!
    Theorem Proving in Lean 4, Section 3
    Propositions and Proofs
    https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html
-/

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => ⟨h.right, h.left⟩)
    (fun h : q ∧ p => ⟨h.right, h.left⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      Or.elim h
        (fun hp : p => Or.inr hp)
        (fun hq : q => Or.inl hq))
    (fun h : q ∨ p =>
      Or.elim h
        (fun hq : q => Or.inr hq)
        (fun hp : p => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
    (fun h : p ∧ (q ∧ r) =>
      ⟨⟨h.left, h.right.left⟩ ,h.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      h.elim
        (fun hp : p ∨ q =>
          hp.elim
            (fun hp2 : p => Or.inl hp2)
            (fun hq2 : q => Or.inr (Or.inl hq2)))
        (fun hr : r => Or.inr (Or.intro_right q hr)))
    (fun h : p ∨ (q ∨ r) =>
      h.elim
        (fun hp : p => Or.inl (Or.intro_left q hp))
        (fun hr : q ∨ r =>
          hr.elim
            (fun hq2: q => Or.inl (Or.inr hq2))
            (fun hr2: r => Or.inr hr2)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      h.right.elim
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      h.elim
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h: p ∨ (q ∧ r) =>
      h.elim
        (fun hp : p =>
          show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inl hp , Or.inl hp⟩)
        (fun hq : q ∧ r =>
          show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inr hq.left, Or.inr hq.right⟩))
    (fun h: (p ∨ q) ∧ (p ∨ r) =>
      have hpq : p ∨ q := h.left
      have hpr : p ∨ r := h.right
      hpq.elim
        (fun hp : p =>
          show p ∨ (q ∧ r) from Or.inl hp)
        (fun hq : q =>
          show p ∨ (q ∧ r) from hpr.elim
            (fun hp : p => Or.inl hp)
            (fun hr : r => Or.inr ⟨hq, hr⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun (h: p → (q → r)) (hpq: p ∧ q) => h (hpq.left) (hpq.right))
    (fun (h: p ∧ q → r) (hp : p) (hq : q) => h ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h: (p ∨ q) → r =>
      ⟨(fun hp: p => h (Or.inl hp)), (fun hq: q => h (Or.inr hq))⟩)
    (fun (h: (p → r) ∧ (q → r)) (hpq: p ∨ q) =>
      hpq.elim
      (fun hp : p => h.left hp)
      (fun hq : q => h.right hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h: ¬(p ∨ q) =>
      ⟨fun (hp: p) => h (Or.inl hp), fun (hq: q) => h (Or.inr hq)⟩)
    (fun (h: ¬p ∧ ¬q) (hpq: p ∨ q) =>
      hpq.elim
        (fun hp: p => h.left hp)
        (fun hq: q => h.right hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (fun (h: ¬p ∨ ¬q) (hpq: p ∧ q) =>
    h.elim
      (fun hp: ¬p => hp hpq.left)
      (fun hq: ¬q => hq hpq.right))

example : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p => h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  (fun (h : p ∧ ¬q) (hpq : p → q) =>
    h.right (hpq h.left))

example : ¬p → (p → q) :=
  fun (h : ¬p) (hp : p) => absurd hp h

example : (¬p ∨ q) → (p → q) :=
  (fun (h : ¬p ∨ q) (hp : p) =>
    h.elim
      (fun hnp : ¬p => absurd hp hnp)
      (fun hq : q => hq))

example : p ∨ False ↔ p :=
  Iff.intro
    (fun h : p ∨ False =>
      h.elim
        (fun hp : p => hp)
        (fun f : False => False.elim f))
    (fun h : p => Or.inl h)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun h : p ∧ False => h.right)
    (fun f : False => False.elim f)

example : (p → q) → (¬q → ¬p) :=
  (fun (h : p → q) (hnq : ¬q) (hp : p) => hnq (h hp))

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  (fun h : p → q ∨ r =>
    Or.elim (em p)
      (fun hp : p =>
        have hpr : q ∨ r := h hp
        hpr.elim
          (fun hq : q => Or.inl (fun _ => hq))
          (fun hr : r => Or.inr (fun _ => hr)))
      (fun hnp : ¬p =>
        Or.inl (fun hp : p => absurd hp hnp)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (fun h: ¬(p ∧ q) =>
    Or.elim (em p)
      (fun hp : p => Or.inr (fun (hq: q) => h ⟨hp, hq⟩))
      (fun hnp : ¬p => Or.inl hnp))

example : ¬(p → q) → p ∧ ¬q :=
  (fun h : ¬(p → q) =>
    Or.elim (em p)
      (fun hp : p => Or.elim (em q)
        (fun hq : q => absurd (fun _ => hq) h)
        (fun hnq : ¬q => ⟨hp, hnq⟩))
      (fun hnp : ¬p => absurd (fun hp : p => absurd hp hnp) h))

example : (p → q) → (¬p ∨ q) :=
  (fun h : p → q =>
    Or.elim (em p)
      (fun hp : p => Or.inr (h hp))
      (fun hnp : ¬p => Or.inl hnp))

example : (¬q → ¬p) → (p → q) :=
  (fun (h : ¬q → ¬p) (hp: p) =>
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd hp (h hnq)))

example : p ∨ ¬p :=
  em p

example : (((p → q) → p) → p) :=
  (fun h : (p → q) → p =>
    Or.elim (em p)
      (fun hp : p => hp)
      (fun hnp : ¬p => h (fun hp : p => absurd hp hnp)))

-- Prove the following statement without using classical logic
example : ¬(p ↔ ¬p) :=
  (fun h : (p ↔ ¬p) =>
    have hnp : ¬p := (fun hp : p => h.mp hp hp);
    hnp (h.mpr hnp))
