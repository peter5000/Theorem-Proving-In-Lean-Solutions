-- Theorem Proving in Lean 4, Section 8
-- Induction and Recursions
-- https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html

-- 1
-- Open a namespace Hidden to avoid naming conflicts, and use the equation compiler to define addition, multiplication, and exponentiation on the natural numbers. Then use the equation compiler to derive some of their basic properties.
namespace Hidden

end Hidden

-- 2
-- Similarly, use the equation compiler to define some basic operations on lists (like the reverse function) and prove theorems about lists by induction (such as the fact that reverse (reverse xs) = xs for any list xs).

-- 3
-- Define your own function to carry out course-of-value recursion on the natural numbers. Similarly, see if you can figure out how to define WellFounded.fix on your own.

-- 4
-- Following the examples in Section Dependent Pattern Matching, define a function that will append two vectors. This is tricky; you will have to define an auxiliary function.

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
  | const n     => sorry
  | var n       => v n
  | plus e₁ e₂  => sorry
  | times e₁ e₂ => sorry

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
-- #eval eval sampleVal sampleExpr

-- Implement "constant fusion," a procedure that simplifies subterms like 5 + 7 to 12. Using the auxiliary function simpConst, define a function "fuse": to simplify a plus or a times, first simplify the arguments recursively, and then apply simpConst to try to simplify the result.

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr := sorry

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e :=
  sorry

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  sorry
