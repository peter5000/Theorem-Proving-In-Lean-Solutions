/-!
    Theorem Proving in Lean 4, Section 4
    Quantifiers and Equality
    https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html
-/

-- Turn off unused variables linter, since some problem statements have
-- unused variables.
set_option linter.unusedVariables false

-- Problem 1. Prove the following equivalences. You should also try to understand why the reverse implication is not derivable in the last example.

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

-- Problem 2. It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable. Try proving these (one direction of the second of these requires classical logic).

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry

open Classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

-- Problem 3. Consider the "barber paradox," that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction.

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry


-- Problem 4. Remember that, without any parameters, an expression of type `Prop` is just an assertion. Fill in the definitions of `prime` and `Fermat_prime` below, and construct each of the given assertions. For example, you can say that there are infinitely many primes by asserting that for every natural number `n`, there is a prime number greater than `n`. Goldbach's weak conjecture states that every odd number greater than 5 is the sum of three primes. Look up the definition of a Fermat prime or any of the other statements, if necessary.

def even (n : Nat) : Prop := sorry
def divides (x y : Nat) : Prop := sorry

infix:50 " ∣ " => divides
def prime (n : Nat) : Prop := sorry
def infinitely_many_primes : Prop := sorry
def Fermat_prime (n : Nat) : Prop := sorry
def infinitely_many_Fermat_primes : Prop := sorry
def goldbach_conjecture : Prop := sorry
def Goldbach's_weak_conjecture : Prop := sorry
def Fermat's_last_theorem : Prop := sorry

-- Problem 5. Prove as many of the identities listed in the Existential Quantifier section as you can.
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
