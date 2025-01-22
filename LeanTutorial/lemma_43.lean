import Mathlib
import LeanTutorial.basic
open Polynomial

variable (n p r : ℕ) (hrnz : r ≠ 0) [hp': Fact (Nat.Prime p)] (hnnoprdivs : no_prime_divisors_below n r) (hnnotperfpow : ¬ is_perfect_power n)  [hge1: Fact (n ≥ 1)] -- use a weaker assumption, have a bit more general lemma

lemma logb_base2_ge_one {n : ℕ} (hn : n ≥ 2) : 1 ≤ Real.logb 2 n := by
    cases n
    exfalso
    exact Nat.not_succ_le_zero 1 hn
    case succ n =>
    rw[Real.le_logb_iff_rpow_le]
    simp
    rw[ge_iff_le] at hn
    rify at hn
    exact hn
    exact one_lt_two
    have : 0 < n + 1 := by
      exact Nat.zero_lt_succ n
    rify at this
    simp
    exact this

lemma nge2 (hn' : p ∣ n) : n ≥ 2 := by
    have pprime := hp'.out
    have nge0 := hge1.out
    have zero_lt_n : 0 < n := lt_of_lt_of_le (zero_lt_one) nge0
    have p_le_n : p ≤ n := Nat.le_of_dvd zero_lt_n hn'
    have pge2 : 2 ≤ p := Nat.Prime.two_le pprime
    apply lt_of_lt_of_le pge2 p_le_n



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
    apply logb_base2_ge_one (nge2 n p hp)
  have eqq := by exact (hX polinH)
  have eqq': (AdjoinRoot.mk (f p r)) 1  = (AdjoinRoot.mk (f p r)) 0 := by
    simp
    exact eqq

  have p_ndiv_one : ¬ p ∣ 1 := Nat.Prime.not_dvd_one (inferInstanceAs (Fact (Nat.Prime p))).out
  have : NeZero (1 : AdjoinRoot (f p r)) := by
    haveI : CharP (AdjoinRoot (f p r)) p := instCharPAdjoinRootF _ _ hrnz
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

  have orderX : orderOf (β p r) = r := order_of_X_in_F p r hrnz
  -- see cyclotomic.lean eventually

  sorry

  --refine ext ?_
  --rintro j


  --rw [hmod, AdjoinRoot.mk_sub],
  --exact sub_self _, modular equality??

-- use order_of_X_in_F
