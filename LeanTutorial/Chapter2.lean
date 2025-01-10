import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Prime.Defs
import Mathlib.Algebra.Polynomial.Basic
import Init.Data.Int.Basic
import Mathlib.Algebra.Divisibility.Basic

theorem primality (n : ℕ) (hn : n ≥ 2) (a : ℤ) (coprime : IsCoprime (↑ n) a)
  : Prime n ↔ Polynomial.C (R := ℤ) (↑ n) ∣ ((X : Polynomial ℤ) + Polynomial.C a)^n - Polynomial.monomial n 1 + Polynomial.C a
  := by sorry

-- define the polynomial in z mod n, it might be easier

-- (n choose k) = 0

-- quotients, morphisms, ideal.quotient.blabla, ring to quotient

theorem n_choose_k (n : ℕ ) (k : ℕ ) (hk1 : k < n) (hk2 : k > 0) (hn : Prime n)
  : n.choose k % n = 0
  := by sorry
