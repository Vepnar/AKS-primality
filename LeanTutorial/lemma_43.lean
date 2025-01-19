import Mathlib
import LeanTutorial.basic
open Polynomial

variable (n p r : ℕ) (hrnz : r ≠ 0) [Fact (Nat.Prime p)] (A : ℕ)

lemma lemma43 (g q : Polynomial (ZMod p)) (hg : AdjoinRoot.mk (h p r) g ∈ Gmonoid n p r hrnz) (hq : AdjoinRoot.mk (h p r) q ∈ Gmonoid n p r hrnz)
  (hmod : AdjoinRoot.mk (h p r) g = AdjoinRoot.mk (h p r) q)
  (hdegg : Polynomial.degree g < R) (hdegq : Polynomial.degree q < R)
  : g = q := by
  let Δ := g - q
  have hΔmod : ∀ k ∈ S n p r, AdjoinRoot.mk (h p r) (Δ.comp X^k) = 0
  intro w -- changed X to w so it is not confused with X variable, you can always change it back
  simp
  intro hX
  rotate_right 1
  rw[AdjoinRoot.mk_eq_mk] at hmod
  rw[dvd_iff_exists_eq_mul_left] at hmod
  cases' hmod with u uu
  rw[sub_eq_iff_eq_add] at uu
  rw[uu]
  rw[add_left_eq_self]
  sorry

  --rw[dvd_iff_exists_eq_mul_left]
  refine And.symm ⟨?_, ?_⟩
  by_contra hw
  -- then since w is in S we have that for all functions g in H g 0 = 1 which does not seem very likely, so maybe that might be the rest of the proof
  sorry

  rw[AdjoinRoot.mk_eq_mk] at hmod
  exact hmod



  --refine ext ?_
  --rintro j


  --rw [hmod, AdjoinRoot.mk_sub],
  --exact sub_self _, modular equality??

-- use order_of_X_in_F
