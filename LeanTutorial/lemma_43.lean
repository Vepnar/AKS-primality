import Mathlib
import LeanTutorial.basic
open Polynomial

variable (n p r : ℕ) (hrnz : r ≠ 0) [Fact (Nat.Prime p)] (hnnoprdivs : no_prime_divisors_below n r) (hnnotperfpow : ¬ is_perfect_power n)  [Fact (n ≥ 1)] -- use a weaker assumption, have a bit more general lemma

lemma lemma43 (g q : Polynomial (ZMod p))
  (hg : AdjoinRoot.mk (h p r) g ∈ Gmonoid n p r hrnz) (hq : AdjoinRoot.mk (h p r) q ∈ Gmonoid n p r hrnz)
  (hmod : AdjoinRoot.mk (h p r) g = AdjoinRoot.mk (h p r) q)
  (hdegg : Polynomial.degree g < Nat.card (R n p r hrnz hp hphnnoprdivs)) (hdegq : Polynomial.degree q < Nat.card (R n p r hrnz hp hnnoprdivs))
  : g = q := by
  let Δ := g - q
  have hΔmod : ∀ k ∈ S n p r, AdjoinRoot.mk (h p r) (Δ.comp X^k) = 0
  intro w -- changed X to w so it is not confused with X variable, you can always change it back
  simp
  intro hX

  constructor
  . rw[AdjoinRoot.mk_eq_mk] at hmod
    exact hmod
  show w ≠ 0
  by_contra hw
  rw[hw] at hX
  unfold S at hX
  simp at hX
  specialize hX (AdjoinRoot.mk (f p r) (X + 1))
  simp at hX
  have polinH: AdjoinRoot.root (f p r) + 1 ∈ H n p r := by
    unfold H
    apply Submonoid.subset_closure
    unfold α
    use 1
    simp
    unfold A
    apply Nat.le_floor
    simp
    refine one_le_mul_of_one_le_of_one_le ?_ ?_
    swap
    rw[Real.one_le_sqrt]
    -- linarith
    simp
    exact Nat.zero_lt_of_ne_zero (by trivial)
    sorry
  have eqq := by exact (hX polinH)
  have eqq': (AdjoinRoot.mk (f p r)) 1  = (AdjoinRoot.mk (f p r)) 0 := by
    simp
    exact eqq

  have p_ndiv_one : ¬ p ∣ 1 := Nat.Prime.not_dvd_one (inferInstanceAs (Fact (Nat.Prime p))).out
  have : NeZero (1 : AdjoinRoot (f p r)) := by
    haveI : CharP (AdjoinRoot (f p r)) p := sorry -- TODO
    have := NeZero.of_not_dvd (AdjoinRoot (f p r)) p_ndiv_one
    simp at *
    assumption

  have contrad := this.out eqq'
  exact contrad

  -- rw[AdjoinRoot.mk_eq_mk] at eqq'
  -- simp at eqq'
  -- rw[dvd_iff_exists_eq_mul_left] at eqq'
  -- cases' eqq' with o1 o2
  -- apply_fun Polynomial.natDegree at o2
  -- rw[Polynomial.natDegree_mul] at o2
  -- simp at o2
  -- have degf : (f p r).natDegree = r := by sorry
  -- --rw[degf] at o2
  -- rw[eq_comm] at o2
  -- rw[Nat.add_eq_zero_iff] at o2
  -- cases' o2 with o2 o3
  -- rw[o3] at degf
  -- rw[eq_comm] at degf
  -- exact (hrnz degf)

  -- by_contra t
  -- rw[t] at o2
  -- simp at o2

  rw[AdjoinRoot.mk_eq_mk, dvd_iff_exists_eq_mul_left] at hmod
  cases' hmod with u uu
  rw[sub_eq_iff_eq_add] at uu
  rw[uu, add_left_eq_self]
  rw[← add_neg_eq_iff_eq_add] at uu
  simp

  have orderX : orderOf (AdjoinRoot.root (h p r)) = r := by sorry
  -- see cyclotomic.lean eventually

  sorry

  --refine ext ?_
  --rintro j


  --rw [hmod, AdjoinRoot.mk_sub],
  --exact sub_self _, modular equality??

-- use order_of_X_in_F
