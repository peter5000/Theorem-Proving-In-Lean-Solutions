/-!
    Theorem Proving in Lean 4, Section 7
    Inductive Types
    https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html
-/

-- Problem 1. Try defining other operations on the natural numbers, such as multiplication, the predecessor function (with `pred 0 = 0`), truncated subtraction (with `n - m = 0` when m is greater than or equal to `n`), and exponentiation. Then try proving some of their basic properties, building on the theorems we have already proved.
-- Since many of the functions you will define below are already in Lean's core library, you should work within a namespace named Hidden in order to avoid name clashes.

namespace Hidden

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

-- The addition operation from the text is provided for you.
def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + Nat.zero = m := rfl
theorem add_succ (m n : Nat) : m + Nat.succ n = Nat.succ (m + n) := rfl
theorem zero_add (n : Nat) : Nat.zero + n = n := by
  induction n <;> simp [*, add_zero, add_succ]
theorem succ_add (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) := by
  induction n <;> simp [*, add_zero, add_succ]
theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k <;> simp [*, add_zero, add_succ]

end Hidden


-- Problem 2. Define some operations on lists, like a length function or the reverse function. Prove some properties, such as the following:
-- a. `length (s ++ t) = length s + length t`
-- b. `length (reverse t) = length t`
-- c. `reverse (reverse t) = t`

-- Some related theorems on List from the text are provided for you.
def append (as bs : List α) : List α :=
 match as with
 | List.nil       => bs
 | List.cons a as => List.cons a (append as bs)

theorem nil_append (as : List α) : append List.nil as = as :=
 rfl

theorem cons_append (a : α) (as bs : List α)
                    : append (List.cons a as) bs = List.cons a (append as bs) :=
 rfl

-- `append_nil` and `append_assoc` are additional exercises to prove before parts (a), (b), (c).
theorem append_nil (as : List α) : append as List.nil = as := by sorry

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) := by sorry

-- Problem 3. Define an inductive data type consisting of terms built up from the following constructors:
-- `const n`, a constant denoting the natural number `n`
-- `var n`, a variable, numbered `n`
-- `plus s t`, denoting the sum of `s` and `t`
-- `times s t`, denoting the product of `s` and `t`
-- Recursively define a function that evaluates any such term with respect to an assignment of values to the variables.

-- Problem 4. Similarly, define the type of propositional formulas, as well as functions on the type of such formulas: an evaluation function, functions that measure the complexity of a formula, and a function that substitutes another formula for a given variable.
