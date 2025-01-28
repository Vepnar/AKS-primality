import Mathlib
import LeanTutorial.basic
import LeanTutorial.distinct_lemma
import LeanTutorial.lemma_41
import LeanTutorial.lemma_42
import LeanTutorial.pdivninS

variable (n p r : ℕ) (hrnz : r ≠ 0) [pprime : Fact (Nat.Prime p)]
  (hp : p ∣ n) (hnnoprdivs : no_prime_divisors_below n r) (hnnotperfpow : ¬ is_perfect_power n) (hnodd : Odd n) (hn_gt_one : n > 1)
  (childs_binomial_theorem : ∀ a ∈ Finset.range (A n r + 1),
    (α p r + ↑ a)^n = α p r^n + ↑ a)
  (hordern : orderOf (↑ n : ZMod r) > ⌊(Real.logb 2 n) ^ 2 ⌋₊)
  (hnnotprime : ¬ n.Prime)

include hnnotperfpow hn_gt_one hnnotprime in
lemma n_not_power_of_p : ∀ k : ℕ, p^k ≠ n
 := λ k f ↦ hnnotperfpow $ by
    use p, k
    constructor
    . exact Nat.Prime.one_lt pprime.out
    constructor
    . by_contra hk
      rw [ge_iff_le, not_le] at hk
      have : k = 0 ∨ k = 1 := by omega
      cases this with
      | inl kzero => simp[kzero] at f; rw[f] at hn_gt_one; exact Nat.lt_irrefl n $ gt_iff_lt.mp hn_gt_one
      | inr kone => simp[kone] at f; rw[← f] at hnnotprime; exact hnnotprime pprime.out
    . exact f

include hnnotperfpow hn_gt_one hnnotprime hp in
lemma n_over_p_not_power_of_p : ∀ k : ℕ, p^k ≠ n/p
 := by
  intro k f
  replace f := calc
    p^(k+1) = p^k * p := rfl
    _ = n/p * p := by rw[f]
    _ = n := Nat.div_mul_cancel hp
  exact n_not_power_of_p n p hnnotperfpow hn_gt_one hnnotprime (k+1) f

noncomputable def T : Finset (ℕ × ℕ)
  := let K := Finset.range $ Nat.floor (Real.sqrt $ Nat.card $ R n p r hrnz hp hnnoprdivs) + 1
    K ×ˢ K

omit pprime in
lemma boundT (ij : ℕ × ℕ) (hij : ij ∈ T n p r hrnz hp hnnoprdivs)
  : ij.1 ≤ (Real.sqrt $ Nat.card $ R n p r hrnz hp hnnoprdivs)
  ∧ ij.2 ≤ (Real.sqrt $ Nat.card $ R n p r hrnz hp hnnoprdivs)
  := by
  simp only [T, Real.nat_floor_real_sqrt_eq_nat_sqrt, Finset.mem_product, Finset.mem_range] at hij
  obtain ⟨hi,hj⟩ := hij
  constructor
  repeat
    exact Trans.trans (Nat.cast_le.mpr (Nat.le_of_lt_succ (by assumption))) Real.nat_sqrt_le_real_sqrt

omit pprime in
lemma cardT : Nat.card (R n p r hrnz hp hnnoprdivs) < Nat.card (T n p r hrnz hp hnnoprdivs)
  := by
  unfold T
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_product,
    Real.nat_floor_real_sqrt_eq_nat_sqrt, Finset.card_range, gt_iff_lt]
  exact Nat.sqrt_lt.mp $ lt_add_one _

def ℓ (ij : ℕ × ℕ) : (ZMod r)ˣ
  := n_over_p' n p r hrnz hp hnnoprdivs ^ ij.1 * p' n p r hrnz hp hnnoprdivs ^ ij.2

include hp hnodd hn_gt_one childs_binomial_theorem hordern in
lemma m_in_S (ij : ℕ × ℕ) : m (n/p) p ij ∈ S n p r
  := by
  apply lemma41 n p r
  repeat' (apply pow_in_S)
  exact ndivpinS n p r hp hnodd hn_gt_one childs_binomial_theorem hordern
  exact pinS n p r

omit pprime in
lemma ℓ_equiv_m (ij : ℕ × ℕ) : (ℓ n p r hrnz hp hnnoprdivs ij).val = (m (n/p) p ij : ZMod r)
  := by
  unfold ℓ m n_over_p' n' p'
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Nat.cast_mul,
    Nat.cast_pow]
  suffices : (n' n r hrnz hnnoprdivs / p' n p r hrnz hp hnnoprdivs).val = (n/p : ZMod r)
  . unfold n' p' at this
    rw[this]
  apply IsUnit.mul_right_cancel (Units.isUnit (p' n p r hrnz hp hnnoprdivs))
  rw [← Units.val_mul, div_mul_cancel]
  unfold p'
  rw [ZMod.coe_unitOfCoprime, ← Nat.cast_mul, Nat.div_mul_cancel hp]
  unfold n'
  rw [ZMod.coe_unitOfCoprime]

lemma div_dist_ineq {a b c : ℕ} (h : a ≡ b [MOD c]) (hab : a ≠ b) : c ≤ Int.natAbs ((a : ℤ) - (b : ℤ))
  := by
  wlog hblta : b < a
  . cases lt_or_gt_of_ne hab.symm with
    | inl hblta' => exact False.elim (hblta hblta')
    | inr hblta => (
      rw [← Int.natAbs_neg, neg_sub]
      exact this h.symm hab.symm hblta)

  rw[← Nat.cast_sub (le_of_lt hblta), Int.natAbs_cast]
  have hzeroltab := Nat.zero_lt_sub_of_lt hblta
  exact Nat.le_of_dvd hzeroltab ((Nat.modEq_iff_dvd' (by linarith)).mp h.symm)

lemma difference_bounded
  (x y c C : ℝ)
  (hx₁ : c ≤ x) (hx₂ : x ≤ C)
  (hy₁ : c ≤ y) (hy₂ : y ≤ C)
  : |x - y| ≤ C - c
  := by
  wlog hxy : 0 ≤ x - y
  . have hyx : x-y ≤ 0 := le_of_not_ge hxy
    replace hyx : 0 ≤ y-x := by simp_all only [sub_nonneg, not_le, tsub_le_iff_right, zero_add]
    have := this y x c C hy₁ hy₂ hx₁ hx₂ hyx
    rw[← abs_neg, neg_sub]
    assumption

  rw [abs_of_nonneg hxy]
  linarith

lemma real_abs_eq_natabs (a b : ℤ) : ((a - b).natAbs : ℝ) = |(a : ℝ) - (b : ℝ)|
  := by
  rw[← Int.cast_sub, ← Int.cast_abs]
  calc
  ((a - b).natAbs : ℝ) = ↑ ((a - b).natAbs : ℤ) := rfl
  _ = ↑ |a - b| := by congr; exact Int.natCast_natAbs (a - b)

include hnodd hn_gt_one hnnotperfpow hnnotprime childs_binomial_theorem hordern in
lemma upper_bound_G : Nat.card (G n p r hrnz) ≤ (n : ℝ)^(Real.sqrt (Nat.card (R n p r hrnz hp hnnoprdivs))) - 1
  := by
  have hn_over_p_gt_one : n/p > 1 := by
    obtain ⟨c, hc⟩ := hp
    rw[hc, mul_comm, Nat.mul_div_cancel _ (Nat.Prime.pos pprime.out)]
    match c with
    | 0 => rw[mul_zero] at hc; rw[hc] at hn_gt_one; contradiction
    | 1  => rw[mul_one] at hc; rw[hc] at hnnotprime; exfalso; exact hnnotprime pprime.out
    | c' + 2 => exact le_add_left (le_refl 2)

  have := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (t := Set.toFinset (R n p r hrnz hp hnnoprdivs)) -- ask Alain
    (by
      simp only [Set.toFinset_card, SetLike.coe_sort_coe]
      have := cardT n p r hrnz hp hnnoprdivs
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe] at this
      rw[Fintype.card_eq_nat_card]
      exact this
      )
    (f := ℓ n p r hrnz hp hnnoprdivs)
    (by
      intro ⟨i, j⟩ _
      unfold ℓ R
      simp only [Set.mem_toFinset, SetLike.mem_coe]
      apply Subgroup.mul_mem
      repeat' (apply Subgroup.pow_mem)
      unfold n_over_p'
      apply Subgroup.div_mem
      repeat (apply Subgroup.subset_closure; simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        true_or, or_true])
    )

  obtain ⟨x,hx,y,hy,hxy₁,hxy₂⟩ := this

  have mxinS : m (n/p) p x ∈ S n p r := m_in_S n p r hp hnodd hn_gt_one childs_binomial_theorem hordern x
  have myinS : m (n/p) p y ∈ S n p r := m_in_S n p r hp hnodd hn_gt_one childs_binomial_theorem hordern y

  have mxeqvmy : m (n/p) p x ≡ m (n/p) p y [MOD r]
    := by
    rw[← ZMod.eq_iff_modEq_nat]
    calc
    (m (n/p) p x : ZMod r) = ℓ n p r hrnz hp hnnoprdivs x := Eq.symm $ ℓ_equiv_m n p r hrnz hp hnnoprdivs x
    _ = ℓ n p r hrnz hp hnnoprdivs y := congrArg _ hxy₂
    _ = m (n/p) p y := ℓ_equiv_m n p r hrnz hp hnnoprdivs y

  have := lemma42 n p r hrnz (m (n/p) p x) (m (n/p) p y) mxinS myinS mxeqvmy
  have part₁ := div_dist_ineq this
    (Function.Injective.ne
      (distinct (n/p) p
        (n_over_p_not_power_of_p n p hp hnnotperfpow hn_gt_one hnnotprime)
        hn_over_p_gt_one)
      hxy₁)

  let sqrt_R := √↑(Nat.card ↥(R n p r hrnz hp hnnoprdivs))

  have lb_mx : (1 : ℝ) ≤ m (n/p) p x := by
    have := lb_m (n/p) p (le_of_lt hn_over_p_gt_one) (Nat.Prime.pos pprime.out) x
    rify at this
    assumption

  have ub_mx : (m (n/p) p x : ℤ) ≤ ((n/p) : ℝ)^sqrt_R * p^sqrt_R
    := by
    have := ub_m (n/p) p
      (le_of_lt hn_over_p_gt_one) (Nat.Prime.pos pprime.out)
      sqrt_R x (boundT n p r hrnz hp hnnoprdivs x hx).1 (boundT n p r hrnz hp hnnoprdivs x hx).2
    rify at this
    rw[Int.cast_natCast]
    rw [Nat.cast_div_charZero hp] at this
    assumption

  have lb_my : (1 : ℝ) ≤ m (n/p) p y := by
    have := lb_m (n/p) p (le_of_lt hn_over_p_gt_one) (Nat.Prime.pos pprime.out) y
    rify at this
    assumption

  have ub_my : (m (n/p) p y : ℤ) ≤ ((n/p) : ℝ)^sqrt_R * p^sqrt_R
    := by
    have := ub_m (n/p) p
      (le_of_lt hn_over_p_gt_one) (Nat.Prime.pos pprime.out)
      sqrt_R y (boundT n p r hrnz hp hnnoprdivs y hy).1 (boundT n p r hrnz hp hnnoprdivs y hy).2
    rify at this
    rw [Nat.cast_div_charZero hp] at this
    assumption

  have := difference_bounded (m (n/p) p x) (m (n/p) p y)
    1 ((n/p)^sqrt_R * p^sqrt_R)
    lb_mx ub_mx
    lb_my ub_my

  simp[sqrt_R] at this

  have n_div_p_nonneg : 0 ≤ (n : ℝ)/(p : ℝ)
    := by
    apply div_nonneg
    repeat (exact Nat.cast_nonneg _)

  calc
  (Nat.card ↥(G n p r hrnz) : ℝ) ≤ ((m (n / p) p x : ℤ) - ↑(m (n / p) p y)).natAbs := by aesop
  _ = |(m (n / p) p x : ℝ) - ↑(m (n / p) p y)| := real_abs_eq_natabs _ _
  _ ≤ ((n/p) : ℝ) ^ sqrt_R  * (p : ℝ) ^ sqrt_R - 1 := this
  _ = ((n/p : ℝ) * (p : ℝ)) ^ sqrt_R - 1 := by rw [Real.mul_rpow n_div_p_nonneg (Nat.cast_nonneg p)]
  _ = (n : ℝ) ^ sqrt_R - 1 := by rw [div_mul_cancel_of_invertible]
  _ ≤ (n : ℝ) ^ √↑(Nat.card ↥(R n p r hrnz hp hnnoprdivs)) - 1 := by
    apply sub_le_sub_right
    apply Real.rpow_le_rpow_of_exponent_le $ Nat.one_le_cast.mpr (le_of_lt hn_gt_one)
    simp[sqrt_R]
