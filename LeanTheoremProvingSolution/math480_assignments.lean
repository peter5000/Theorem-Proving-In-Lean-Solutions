import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

/- Supply proofs for 2 out of the 3 assignments.
   Do all 3 for 5 points of extra credit.

   All assignments can be proven through induction and appropriate use of library functions and logic operations.
-/

-- Assignment 1: Show that 2^n % 7 = 1, 2, or 4 for all n.
theorem assignment1 : ∀ n:ℕ, 2 ^ n % 7 = 1 ∨ 2^n % 7 = 2 ∨ 2^n % 7 = 4 := by
  intro n
  induction n with
  | zero      => simp
  | succ n ih =>
    rw[Nat.pow_add]
    rw[mul_comm]
    simp[Nat.mul_mod]
    cases ih with
    | inl left  => rw[left]; simp
    | inr right =>
      cases right with
      | inl h2 => rw[h2]; simp
      | inr h4 => rw[h4]; simp

-- Assignment 2: Show that (1-x)*(1+x+x^2+...+x^{n-1}) = (1-x^n)
theorem assignment2
    (x:ℝ)
    : ∀ n:ℕ, (1-x)*(∑ i ∈ Finset.range n, x^i) = 1-x^n := by
  intro n
  induction n with
  | zero      => simp
  | succ n ih =>
    calc (1 - x) * ∑ i ∈ Finset.range (n + 1), x ^ i
    _ = (1 - x) * (∑ i ∈ Finset.range (n), x ^ i + x^(n)) := by simp[Finset.sum_range_succ]
    _ = (1 - x) * (∑ i ∈ Finset.range (n), x ^ i) + (1 - x) * x^(n) := by simp[mul_add]
    _ = (1 - x ^ n) + (1 - x) * x^(n) := by rw[ih]
    _ = (1 - x ^ n) + (- x + 1) * x^(n) := by rw(config := { occs := .pos [2]}) [sub_eq_neg_add]
    _ = (1 - x ^ n) + (- x * x^(n) + 1 * x^(n)) := by rw[Distrib.right_distrib]
    _ = 1 - x * x^(n) := by simp[neg_add_eq_sub]
    _ = 1 - x^(n+1) := by simp[pow_succ, mul_comm]

-- Assignment 3: Show that if a_0 = 0, a_{n+1} = 2*a_n+1 then a_n = 2^n-1.
theorem assignment3
    (a: ℕ → ℝ) (h_zero: a 0 = 0) (h_rec: ∀ n:ℕ, a (n+1) = 2 * (a n) + 1)
    : ∀ n:ℕ, a n = 2^n - 1 := by
  intro n
  induction n with
  | zero      => simp[h_zero]
  | succ n ih =>
    calc a (n + 1)
    _ = 2 * a n + 1 := by rw[h_rec]
    _ = 2 * (2 ^ n - 1) + 1 := by rw[ih]
    _ = 2 * (-1 + 2 ^ n) + 1 := by rw[sub_eq_neg_add]
    _ = -2 + 2 * 2 ^ n + 1 := by simp[Distrib.left_distrib]
    _ = -2 + 2 ^ (n + 1) + 1 := by simp[mul_comm, pow_succ]
    _ = 2 ^ (n + 1) - 1 := by ring
