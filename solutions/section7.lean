-- Theorem Proving in Lean 4, Section 7
-- Inductive Types
-- https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html

-- Other Recursive Data Types
namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α
namespace List
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl
theorem append_nil (as : List α) : append as nil = as := by
  induction as <;> simp[*, append]

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) := by
  induction as <;> simp[*, append]

end List
end Hidden

-- 1

namespace Hidden

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

#print add

instance : Add Nat where
  add := add

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


open Nat
#eval (succ (succ zero)) * (succ zero) -- Hidden.Nat.succ (Hidden.Nat.succ (Hidden.Nat.zero))

theorem add_zero (n : Nat) : n + zero = n := rfl

theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

theorem zero_add (n : Nat) : zero + n = n := by
  induction n <;> simp [*, add_zero, add_succ]

theorem succ_add (m n : Nat) : succ m + n = succ (m + n) := by
  induction n <;> simp [*, add_zero, add_succ]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k <;> simp [*, add_zero, add_succ]

theorem mul_zero (n : Nat) : n * zero = zero := rfl

theorem mul_succ (m n : Nat) : m * succ n = m + (m * n) := rfl

theorem zero_mul (n : Nat) : zero * n = zero := by
  induction n <;> simp [*, mul_zero, mul_succ, add_zero]

theorem succ_mul (m n : Nat) : succ m * n = (m * n) + n := by
  induction n <;> simp [*, mul_zero, mul_succ, add_zero, add_succ, succ_add, add_assoc]

theorem mul_comm (m n : Nat) : m * n = n * m := by
  induction n <;> simp [*, mul_zero, mul_succ, zero_mul, succ_mul, add_comm]

theorem mul_dist (m n k : Nat) : m * (n + k) = (m * n) + (m * k) := by
  induction m <;> simp [*, zero_mul, succ_mul, add_zero, add_assoc, ←add_assoc, add_comm]

theorem mul_assoc (m n k : Nat) : m * n * k = m * (n * k) := by
  induction k <;> simp [*, mul_zero, mul_succ, mul_dist]

end Hidden

-- 2
def length {α : Type u} (as : List α) : Nat :=
  match as with
  | List.nil       => 0
  | List.cons _ as => (length as) + 1

def l := [1, 2, 3]
#eval length l      -- 3

def reverse {α : Type u} (as : List α) : List α :=
  match as with
  | List.nil       => List.nil
  | List.cons a as => List.append (reverse as) [a]

-- a. length (s ++ t) = length s + length t
theorem lpl_eq (s t : List α) : length (s ++ t) = length s + length t := by
  induction s with
  | nil          => simp [length, List.append]
  | cons _ as ih => simp [length, List.append, ih, Nat.add_comm, Nat.add_assoc]

-- b. length (reverse s) = length s
theorem lr_eq (s : List α) : length (reverse s) = length s := by
  induction s with
  | nil          => simp [length]
  | cons _ as ih => simp [length, reverse, lpl_eq, ih]

-- c. reverse (reverse s) = s
theorem raab_eq (as bs : List α) : reverse (List.append as bs) = List.append (reverse bs) (reverse as) := by
  induction as with
  | nil          => simp [reverse]
  | cons _ as ih =>
    rw[List.append]
    rw[reverse]
    rw[ih]
    simp[List.append, reverse]

theorem rr_eq (s : List α) : reverse (reverse s) = s := by
  induction s with
  | nil          => simp [reverse]
  | cons _ as ih =>
    rw[reverse]
    rw[raab_eq]
    simp[ih, reverse]

-- 3
-- Define an inductive data type consisting of terms built up from the following constructors:

-- const n, a constant denoting the natural number n
-- var n, a variable, numbered n (a_n)
-- plus s t, denoting the sum of s and t
-- times s t, denoting the product of s and t
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

-- 4
-- Similarly, define the type of propositional formulas, as well as functions on the type of such formulas: an evaluation function, functions that measure the complexity of a formula, and a function that substitutes another formula for a given variable.

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

-- #reduce (subs formula (p_type.not (p_type.and p_type.True (p_type.var 3))))
-- (subs formula (p_type.not (p_type.and p_type.True (p_type.var 3))))
