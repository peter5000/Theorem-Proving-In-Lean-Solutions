/-!
    Theorem Proving in Lean 4, Section 7
    Inductive Types
    https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html
-/

-- Problem 1. Try defining other operations on the natural numbers, such as multiplication, the predecessor function (with `pred 0 = 0`), truncated subtraction (with `n - m = 0` when m is greater than or equal to `n`), and exponentiation. Then try proving some of their basic properties, building on the theorems we have already proved.

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

def mul (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.zero
  | Nat.succ n => m + (mul m n)

instance : Mul Nat where
  mul := mul

def pred (m : Nat) : Nat :=
  match m with
  | Nat.zero   => Nat.zero
  | Nat.succ m => m

def truncSub (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n =>
    match m with
    | Nat.zero   => Nat.zero
    | Nat.succ m => truncSub m n

def exponentiation (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.succ Nat.zero
  | Nat.succ n => m * (exponentiation m n)

theorem mul_zero (n : Nat) : n * Nat.zero = Nat.zero := rfl

theorem mul_succ (m n : Nat) : m * Nat.succ n = m + (m * n) := rfl

theorem zero_mul (n : Nat) : Nat.zero * n = Nat.zero := by
  induction n <;> simp [*, mul_zero, mul_succ, add_zero]

theorem succ_mul (m n : Nat) : Nat.succ m * n = (m * n) + n := by
  induction n <;> simp [*, mul_zero, mul_succ, add_zero, add_succ, succ_add, add_assoc]

theorem mul_comm (m n : Nat) : m * n = n * m := by
  induction n <;> simp [*, mul_zero, mul_succ, zero_mul, succ_mul, add_comm]

theorem mul_dist (m n k : Nat) : m * (n + k) = (m * n) + (m * k) := by
  induction m <;> simp [*, zero_mul, succ_mul, add_zero, add_assoc, ←add_assoc, add_comm]

theorem mul_assoc (m n k : Nat) : m * n * k = m * (n * k) := by
  induction k <;> simp [*, mul_zero, mul_succ, mul_dist]

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

-- `append_nil` and `append_assoc` are additional exercises to prove.
theorem append_nil (as : List α) : append as List.nil = as := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [cons_append, ih]

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [cons_append, cons_append, cons_append, ih]

def length {α : Type u} (as : List α) : Nat :=
  match as with
  | List.nil       => 0
  | List.cons _ as => (length as) + 1

def reverse {α : Type u} (as : List α) : List α :=
  match as with
  | List.nil       => List.nil
  | List.cons a as => append (reverse as) [a]

-- a. `length (s ++ t) = length s + length t`
theorem lpl_eq (s t : List α) : length (append s t) = length s + length t := by
  induction s with
  | nil          => simp [length, append]
  | cons _ as ih => simp [length, append, ih, Nat.add_comm, Nat.add_assoc]

-- b. `length (reverse t) = length t`
theorem lr_eq (s : List α) : length (reverse s) = length s := by
  induction s with
  | nil          => rfl
  | cons a as ih => simp only [reverse, lpl_eq, ih, length]

-- c. `reverse (reverse t) = t`
theorem raab_eq (as bs : List α) : reverse (append as bs) = append (reverse bs) (reverse as) := by
  induction as with
  | nil          => simp only [nil_append, reverse, append_nil]
  | cons a as ih => rw [append, reverse, ih, append_assoc, reverse]

theorem rr_eq (s : List α) : reverse (reverse s) = s := by
  induction s with
  | nil          => rfl
  | cons a as ih =>
    simp only [reverse, raab_eq, ih, nil_append, append]

-- Problem 3. Define an inductive data type consisting of terms built up from the following constructors:
-- `const n`, a constant denoting the natural number `n`
-- `var n`, a variable, numbered `n`
-- `plus s t`, denoting the sum of `s` and `t`
-- `times s t`, denoting the product of `s` and `t`
-- Recursively define a function that evaluates any such term with respect to an assignment of values to the variables.

inductive d_type where
  | const : Nat → d_type
  | var   : Nat → d_type
  | plus  : d_type → d_type → d_type
  | times : d_type → d_type → d_type

def evaluate (as : Nat → Nat) (d : d_type) : Nat :=
  match d with
  | d_type.const n   => n
  | d_type.var   n   => as n
  | d_type.plus  s t => (evaluate as s) + (evaluate as t)
  | d_type.times s t => (evaluate as s) * (evaluate as t)

-- Problem 4. Similarly, define the type of propositional formulas, as well as functions on the type of such formulas: an evaluation function, functions that measure the complexity of a formula, and a function that substitutes another formula for a given variable.

inductive p_type where
  | True  : p_type
  | False : p_type
  | and   : p_type → p_type → p_type
  | or    : p_type → p_type → p_type
  | not   : p_type → p_type
  | var   : Nat    → p_type

def evalp (v : Nat → Bool) (pt : p_type) : Bool :=
  match pt with
  | p_type.True    => True
  | p_type.False   => False
  | p_type.and p q => evalp v p ∧ evalp v q
  | p_type.or  p q => evalp v p ∨ evalp v q
  | p_type.not p   => ¬ evalp v p
  | p_type.var n   => v n

def compl (pt : p_type) : Nat :=
  match pt with
  | p_type.True    => 1
  | p_type.False   => 1
  | p_type.and p q => compl p + compl q
  | p_type.or  p q => compl p + compl q
  | p_type.not p   => compl p
  | p_type.var _   => 1

def subs (form : Nat → p_type) (org : p_type) : p_type :=
  match org with
  | p_type.True    => p_type.True
  | p_type.False   => p_type.False
  | p_type.and p q => p_type.and (subs form p) (subs form q)
  | p_type.or  p q => p_type.or (subs form p) (subs form q)
  | p_type.not p   => p_type.not (subs form p)
  | p_type.var n   => form n

def formula : Nat → p_type
  | 0 => p_type.and (p_type.not p_type.True) p_type.True
  | _ => p_type.or p_type.True p_type.False
