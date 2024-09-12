/-!
    Theorem Proving in Lean 4, Section 8
    Induction and Recursion
    https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html
-/

-- Problem 1. Open a namespace `Hidden` to avoid naming conflicts, and use the equation compiler to define addition, multiplication, and exponentiation on the natural numbers. Then use the equation compiler to derive some of their basic properties.
namespace Hidden

end Hidden

-- Problem 2. Similarly, use the equation compiler to define some basic operations on lists (like the `reverse` function) and prove theorems about lists by induction (such as the fact that `reverse (reverse xs) = xs` for any list `xs`).

-- Problem 3. Define your own function to carry out course-of-value recursion on the natural numbers. Similarly, see if you can figure out how to define `WellFounded.fix` on your own.

-- Problem 4. Following the examples in the section "Dependent Pattern Matching", define a function that will append two vectors. This is tricky; without the equation compiler, you would have to define an auxiliary function.

-- Problem 5. Consider the following type of arithmetic expressions. The idea is that `var n` is a variable, `vₙ`, and `const n` is the constant whose value is `n`.

inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

def eval (v : Nat → Nat) : Expr → Nat
  | Expr.const n     => sorry
  | Expr.var n       => v n
  | Expr.plus e₁ e₂  => sorry
  | Expr.times e₁ e₂ => sorry

-- Implement "constant fusion," a procedure that simplifies subterms like `5 + 7` to `12`. Using the auxiliary function `simpConst`, define a function `fuse`: to simplify a plus or a times, first simplify the arguments recursively, and then apply `simpConst` to try to simplify the result.

def simpConst : Expr → Expr
  | Expr.plus (Expr.const n₁) (Expr.const n₂)  => Expr.const (n₁ + n₂)
  | Expr.times (Expr.const n₁) (Expr.const n₂) => Expr.const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr := sorry

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e :=
  sorry

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  sorry
