/-!
    Theorem Proving in Lean 4, Section 8
    Induction and Recursion
    https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html
-/

-- Problem 1. Open a namespace `Hidden` to avoid naming conflicts, and use the equation compiler to define addition, multiplication, and exponentiation on the natural numbers. Then use the equation compiler to derive some of their basic properties.

namespace Hidden

open Nat

def add : Nat → Nat → Nat
  | m , 0     => m
  | m , n + 1 => succ (add m n)

def mul : Nat → Nat → Nat
  | _, zero   => zero
  | n, succ m => add (mul n m) n

def exp : Nat → Nat → Nat
  | _, zero   => succ zero
  | n, succ m => mul n (exp n m)

theorem add_zero (m : Nat) : add m zero = m := rfl
theorem add_succ (m n : Nat) :add m (succ n) = succ (add m n) := rfl
theorem zero_add : ∀ n, add zero n = n
  | zero   => rfl
  | succ n => congrArg succ (zero_add n)

end Hidden

-- Problem 2. Similarly, use the equation compiler to define some basic operations on lists (like the `reverse` function) and prove theorems about lists by induction (such as the fact that `reverse (reverse xs) = xs` for any list `xs`).

def reverse (as : List α) : List α :=
  let rec loop : List α → List α
    | []    => []
    | a::as => loop as ++ [a]
  loop as

theorem ra_single_eq (xs : List α) (x : α) :
    reverse.loop (xs ++ [x]) = x :: reverse xs := by
  induction xs with
  | nil =>
    simp[reverse.loop, reverse]
  | cons y ys ih =>
    simp[reverse.loop]
    rw[ih]
    simp[List.cons_append, reverse, reverse.loop]

theorem rr_eq (as : List α) : reverse (reverse as) = as := by
  let rec aux (as : List α)
              : (reverse.loop (reverse.loop as)) = as := by
    match as with
    | []    => simp[reverse.loop]
    | a::as => simp[reverse.loop, aux as, ra_single_eq, reverse]
  exact aux as

-- Problem 3. Define your own function to carry out course-of-value recursion on the natural numbers. Similarly, see if you can figure out how to define `WellFounded.fix` on your own.
namespace Hidden
open Nat

theorem mod_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def mod.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (mod_lemma h) y
  else
    x

noncomputable def mod := WellFounded.fix (measure id).wf mod.F
end Hidden

-- Problem 4. Following the examples in the section "Dependent Pattern Matching", define a function that will append two vectors. This is tricky; without the equation compiler, you would have to define an auxiliary function.

inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

def append : {n m : Nat} → (v₁ : Vector α n) → (v₂ : Vector α m) → Vector α (n + m)
  | 0, 0, Vector.nil, Vector.nil => Vector.nil
  | _, 0, as, Vector.nil => as
  | 0, m+1, Vector.nil, Vector.cons a as =>
    Vector.cons a (append Vector.nil as)
  | n+1, m+1, Vector.cons a as, Vector.cons b bs =>
    Vector.cons a (append (append as (Vector.cons b Vector.nil)) bs)

-- Problem 5. Consider the following type of arithmetic expressions. The idea is that `var n` is a variable, `vₙ`, and `const n` is the constant whose value is `n`.
inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => eval v e₁ + eval v e₂
  | times e₁ e₂ => eval v e₁ * eval v e₂

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr
  | plus  e1 e2 => simpConst (plus (fuse e1) (fuse e2))
  | times e1 e2 => simpConst (times (fuse e1) (fuse e2))
  | e           => simpConst e

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e := by
  intro e
  induction e with
  | const n => rfl
  | var n => rfl
  | plus e1 e2 =>
    cases e1 with
    | const n1 =>
      cases e2 with
      | const n2 => simp[simpConst, eval]
      | _ => simp[simpConst]
    | _ => simp[simpConst]
  | times e1 e2 =>
    cases e1 with
    | const n1 =>
      cases e2 with
      | const n2 => simp[simpConst, eval]
      | _ => simp[simpConst]
    | _ => simp[simpConst]

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e := by
  intro e
  induction e with
  | const n => rfl
  | var n => rfl
  | plus e₁ e₂ ih₁ ih₂ =>
    calc
      eval v (fuse (plus e₁ e₂))
      _ = eval v (simpConst (plus (fuse e₁) (fuse e₂))) := by rw[fuse]
      _ = eval v (plus (fuse e₁) (fuse e₂)) := by rw[simpConst_eq]
      _ = eval v (fuse e₁) + eval v (fuse e₂) := by rw[eval]
      _ = eval v e₁ + eval v e₂ := by rw[ih₁, ih₂]
      _ = eval v (plus e₁ e₂) := by rw[eval]
  | times e₁ e₂ ih₁ ih₂ =>
    calc
      eval v (fuse (times e₁ e₂))
      _ = eval v (simpConst (times (fuse e₁) (fuse e₂))) := by rw[fuse]
      _ = eval v (times (fuse e₁) (fuse e₂)) := by rw[simpConst_eq]
      _ = eval v (fuse e₁) * eval v (fuse e₂) := by rw[eval]
      _ = eval v e₁ * eval v e₂ := by rw[ih₁, ih₂]
      _ = eval v (times e₁ e₂) := by rw[eval]
