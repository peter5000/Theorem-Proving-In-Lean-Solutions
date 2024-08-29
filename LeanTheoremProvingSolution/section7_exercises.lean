-- Theorem Proving in Lean 4, Section 7
-- Inductive Types
-- https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html

-- 1
-- Try defining other operations on the natural numbers, such as multiplication, the predecessor function (with pred 0 = 0), truncated subtraction (with n - m = 0 when m is greater than or equal to n), and exponentiation. Then try proving some of their basic properties, building on the theorems we have already proved.

-- Since many of these are already defined in Lean's core library, you should work within a namespace named Hidden, or something like that, in order to avoid name clashes.

-- 2
-- Define some operations on lists, like a length function or the reverse function. Prove some properties, such as the following:

-- a. length (s ++ t) = length s + length t

-- b. length (reverse t) = length t

-- c. reverse (reverse t) = t

-- 3
-- Define an inductive data type consisting of terms built up from the following constructors:

-- const n, a constant denoting the natural number n
-- var n, a variable, numbered n
-- plus s t, denoting the sum of s and t
-- times s t, denoting the product of s and t
-- Recursively define a function that evaluates any such term with respect to an assignment of values to the variables.

-- 4
-- Similarly, define the type of propositional formulas, as well as functions on the type of such formulas: an evaluation function, functions that measure the complexity of a formula, and a function that substitutes another formula for a given variable.
