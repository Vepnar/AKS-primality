import Mathlib
open Polynomial

variable (p : ℕ) [Fact (Nat.Prime p)]

def 𝔽pbar (p : ℕ) [Fact (Nat.Prime p)]
  := AlgebraicClosure (ZMod p)

noncomputable instance 𝔽pbar_instField : Field (𝔽pbar p)
  := by unfold 𝔽pbar; infer_instance

noncomputable instance 𝔽pbar_instAlgebra : Algebra (ZMod p) (𝔽pbar p)
  := by unfold 𝔽pbar; infer_instance

lemma cyclotomic_over_Fp (p r : ℕ) [Fact (Nat.Prime p)] (coprime : p.Coprime r)
  : cyclotomic' r (𝔽pbar p) = cyclotomic r (𝔽pbar p)
  := by
  induction' r using Nat.strong_induction_on with k ih
  rw[Polynomial.cyclotomic'_eq_X_pow_sub_one_div,Polynomial.cyclotomic_eq_X_pow_sub_one_div]
  suffices : ∀ i ∈ k.properDivisors, cyclotomic' i (𝔽pbar p) = cyclotomic i (𝔽pbar p)
  . have : ∏ i ∈ k.properDivisors, cyclotomic' i (𝔽pbar p) = ∏ i ∈ k.properDivisors, cyclotomic i (𝔽pbar p) := by
      apply Finset.prod_congr
      . rfl
      . intro i hi
        apply ih
        . exact (Nat.mem_properDivisors.mp hi).2
        . apply Nat.Coprime.of_dvd_right (Nat.mem_properDivisors.mp hi).1
          assumption
    rw[this]

  . sorry
