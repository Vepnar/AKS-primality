import Mathlib

def no_prime_divisors (n : ℕ) (r : ℕ): Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬(p ∣ n ∧ p ≤ r)
