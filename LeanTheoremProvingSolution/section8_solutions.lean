-- Theorem Proving in Lean 4, Section 8
-- Induction and Recursions
-- https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html

-- 1
-- Open a namespace Hidden to avoid naming conflicts, and use the equation compiler to define addition, multiplication, and exponentiation on the natural numbers. Then use the equation compiler to derive some of their basic properties.
namespace Hidden

open Nat

def add : Nat → Nat → Nat
  | m , 0     => m
  | m , n + 1 => succ (add m n)

#print add

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

-- 2
-- Similarly, use the equation compiler to define some basic operations on lists (like the reverse function) and prove theorems about lists by induction (such as the fact that reverse (reverse xs) = xs for any list xs).

def reverse (as : List α) : List α :=
  let rec loop : List α → List α
    | []    => []
    | a::as => loop as ++ [a]
  loop as

#check reverse
#eval reverse [3,2,1]

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

-- 3
-- Define your own function to carry out course-of-value recursion on the natural numbers. Similarly, see if you can figure out how to define WellFounded.fix on your own.
open Nat

theorem mod_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def mod.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (mod_lemma h) y
  else
    x

noncomputable def mod := WellFounded.fix (measure id).wf mod.F

#reduce mod 23 8 -- 7

-- 4
-- Following the examples in Section Dependent Pattern Matching, define a function that will append two vectors. This is tricky; you will have to define an auxiliary function.

inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

#check @Vector.casesOn


end Vector

def appendAux (v1 : Vector α m) (v2 : Vector α n) : Vector α (m + n) :=
  Vector.casesOn (motive := fun x _ => Vector α (x + n)) v1
    (fun (a : α) (m : Nat) (as : Vector α m) =>
      Vector.casesOn (motive := fun y _ => Vector α (m + y)) v2)
    -- (α → {n_1 : Nat} → Vector α n_1 → Vector α (m + n)) → Vector α (m + n)

def append {α : Type u} {n m : Nat} (v₁ : Vector α n) (v₂ : Vector α m) : Vector α (n + m) :=
  appendAux v₁ v₂


def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vector α m) =>
     fun (h : m + 1 = n + 1) =>
       Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vector α (n+1)) : Vector α n :=
  tailAux v rfl

-- 5
inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => eval v e₁ + eval v e₂
  | times e₁ e₂ => eval v e₁ * eval v e₂

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
-- #eval eval sampleVal sampleExpr

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
