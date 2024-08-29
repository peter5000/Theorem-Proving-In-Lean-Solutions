-- Theorem Proving in Lean 4, Section 4
-- Quantifiers and Equality
-- https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html

-- 1
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun (h : ∀ x, p x ∧ q x) =>
      ⟨fun x => (h x).left, fun x => (h x).right⟩)
    (fun (h : (∀ x, p x) ∧ (∀ x, q x)) =>
      fun x => ⟨h.left x, h.right x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun (h1 : ∀ x, p x → q x) (h2 : ∀ x, p x) =>
    fun x => h1 x (h2 x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun (h : (∀ x, p x) ∨ (∀ x, q x)) =>
    fun x => h.elim
        (fun (hp : ∀ x, p x) => Or.inl (hp x))
        (fun (hq : ∀ x, q x) => Or.inr (hq x))

-- 2
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun h : α =>
    Iff.intro
      (fun (hxr : ∀ _, r) => hxr h)
      (fun (hr : r) => (fun _ => hr))

open Classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h : ∀ x, p x ∨ r =>
      (em r).elim
        (fun hr: r => Or.inr hr)
        (fun hnr: ¬r => Or.inl
          (fun x => (h x).elim
            (fun hpx : p x => hpx)
            (fun hr : r => absurd hr hnr))))
    (fun h : (∀ x, p x) ∨ r => h.elim
      (fun hpx : (∀ x, p x) => (fun x => Or.inl (hpx x)))
      (fun hr : r => (fun _ => Or.inr hr)))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun (h : ∀ x, r → p x) (hr : r) =>
      (fun x => h x hr))
    (fun (h : r → ∀ x, p x) =>
      (fun x => (fun hr: r => h hr x)))

-- 3
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  (h barber).mp
    ((h barber).mpr
      (fun hsbb : shaves barber barber => (h barber).mp hsbb hsbb))
  ((h barber).mpr
      fun hsbb : shaves barber barber => (h barber).mp hsbb hsbb)

-- 4
def even (n : Nat) : Prop :=
  ∃ (z : Nat), (z = 2 * n)

def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

infix:50 " ∣ " => divides

def prime (n : Nat) : Prop :=
  2 ≤ n ∧ ∀x : Nat, (∃ k : Nat, k*x = n) ∧ ¬(∃y : Nat, x = y ∧ ¬(y = 1) ∧ ¬(y = n))

def infinitely_many_primes : Prop :=
  ∀n : Nat, (∃x, (prime x) ∧ (x > n))

def Fermat_prime (n : Nat) : Prop :=
  (prime n) ∧ ∃x : Nat, n = 2*x + 1

def infinitely_many_Fermat_primes : Prop :=
  ∀n : Nat, (∃x, (Fermat_prime x) ∧ (x > n))

def goldbach_conjecture : Prop :=
  ∀x : Nat, (x > 2) ∧ (even x) → ∃y:Nat, ∃z:Nat, (prime y) ∧ (prime z) ∧ x = y + z

def Goldbach's_weak_conjecture : Prop :=
  ∀x : Nat, ¬(even x) ∧ (x > 5) → ∃a:Nat, ∃b : Nat, ∃c : Nat, (prime a) ∧ (prime b) ∧ (prime c) ∧ x = a + b + c

def Fermat's_last_theorem : Prop :=
  ∀a : Nat, ∀b : Nat, ∀c: Nat, ∀n :Nat, (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (n > 2) ∧ ¬(a^n + b^n = c^n)

-- 5
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun ⟨x, hr⟩ => hr

example (a : α) : r → (∃ x : α, r) :=
  fun (hr : r) => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun ⟨x, hpx, hr⟩ => ⟨⟨x, hpx⟩, hr⟩)
    (fun h : (∃ x, p x) ∧ r =>
      match h.left with
      | ⟨w, hpx⟩ => ⟨w, hpx, h.right⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨w, hpq⟩ =>
        hpq.elim
          (fun hp : p w => Or.inl ⟨w, hp⟩)
          (fun hq : q w => Or.inr ⟨w, hq⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      h.elim
        (fun ⟨w, hpx⟩ => ⟨w, Or.inl hpx⟩)
        (fun ⟨w, hqx⟩ => ⟨w, Or.inr hqx⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h : ∀ x, p x =>
      fun ⟨w, hnpw⟩ => hnpw (h w))
    (fun h : ¬ (∃ x, ¬ p x) =>
      fun x => (em (p x)).elim
        (fun hpx => hpx)
        (fun hnpx => absurd ⟨x, hnpx⟩ h))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun ⟨w, hpx⟩ =>
      fun hnpx : ∀ x, ¬ p x => hnpx w hpx)
    (fun h : ¬ (∀ x, ¬ p x) =>
      (em (∃x,p x)).elim
        (fun hpx => hpx)
        (fun hnpx => absurd (fun x => fun px => hnpx (Exists.intro x px)) h))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h : ¬ ∃ x, p x => (fun x => fun hpx => h ⟨x, hpx⟩))
    (fun h : ∀ x, ¬ p x =>
      fun ⟨x, px⟩ => h x px)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h : ¬ ∀ x, p x =>
      byContradiction
        (fun hnp' : ¬∃ x, ¬p x =>
          h (fun x =>
            byContradiction
              (fun hnpx => hnp' ⟨x, hnpx⟩))))
    (fun ⟨x, hnpx⟩ =>
      (fun h => hnpx (h x)))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun (h : ∀ x, p x → r) (⟨x, px⟩) => h x px)
    (fun (h : (∃ x, p x) → r) => (fun x => fun hpx => h ⟨x, hpx⟩))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun (⟨x, hpxr⟩) (h : ∀ x, p x) => hpxr (h x))
    (fun (h : (∀ x, p x) → r) =>
      match (em (∀ x, p x)) with
      | Or.inl hpx => ⟨a, (fun _ => h hpx)⟩
      | Or.inr hnpx =>
        byContradiction
          (fun hnex : ¬ ∃ x, p x → r =>
              have hpx : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    hnex hex)
              hnpx hpx))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨x, hrpx⟩ (hr: r) =>
      ⟨x, hrpx hr⟩)
    (fun h : r → ∃ x, p x =>
      match (em r) with
      | Or.inl hr =>
        have ⟨a, hpx⟩ := h hr; ⟨a, fun _ => hpx⟩
      | Or.inr hnr => ⟨a, fun hr => absurd hr hnr⟩)
