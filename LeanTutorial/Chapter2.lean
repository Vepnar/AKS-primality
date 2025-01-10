import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Prime.Defs
import Mathlib.Algebra.Polynomial.Basic
import Init.Data.Int.Basic
import Mathlib.Algebra.Divisibility.Basic

theorem primality (n : ℕ) (hn : n ≥ 2) (a : ℤ) (coprime : IsCoprime (↑ n) a)
  : Prime n ↔ Polynomial.C (R := ℤ) (↑ n) ∣ ((X : Polynomial ℤ) + Polynomial.C a)^n - Polynomial.monomial n 1 + Polynomial.C a
  := by sorry
