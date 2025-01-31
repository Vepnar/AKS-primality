import Mathlib
import AKS.basic
import AKS.lemma_43

variable (n p r : ℕ) (hrnz : r ≠ 0) [pprime : Fact (Nat.Prime p)]
  (hp : p ∣ n) (hnnoprdivs : no_prime_divisors_below n r) (hnnotperfpow : ¬ is_perfect_power n) (hnodd : Odd n) (hn_gt_one : n > 1)
  (childs_binomial_theorem : ∀ a ∈ Finset.range (A n r + 1),
    (α p r + ↑ a)^n = α p r^n + ↑ a)
  (hordern : orderOf (↑ n : ZMod r) > ⌊(Real.logb 2 n) ^ 2⌋₊)

omit [Fact (Nat.Prime p)] in
lemma ord_R : Nat.card (R n p r hrnz hp hnnoprdivs) ≥ d n r := by
  -- for in the report: this is definition no. 3
  -- first I tried making it a subgroup of R
  -- then I defined it as Subgroup.closure {n' n r hrnz hnnoprdivs}.
  -- this is definitely best
  let sub : Subgroup (ZMod r)ˣ := Subgroup.zpowers (n' n r hrnz hnnoprdivs)
  have sub_in_R : sub ≤ R n p r hrnz hp hnnoprdivs := by
    apply Subgroup.zpowers_le_of_mem
    apply Subgroup.subset_closure
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]

  suffices : Nat.card sub = d n r
  . rw[← this]
    exact Subgroup.card_le_of_le sub_in_R

  have ninsub : n' n r hrnz hnnoprdivs ∈ sub := by
    simp only [Subgroup.mem_zpowers, sub]

  rw [Nat.card_zpowers]
  simp only [Subgroup.orderOf_mk, n', ← orderOf_units, ZMod.coe_unitOfCoprime]
  rfl

omit pprime in
lemma ord_R₂ : Nat.card (R n p r hrnz hp hnnoprdivs) ≤ r := by
  trans Nat.card (ZMod r)ˣ
  . exact Subgroup.card_le_card_group (R n p r hrnz hp hnnoprdivs)
  trans Nat.card (ZMod r)
  -- TODO: refactor everything to replace hrnz by a typeclass argument
  . haveI : NeZero r := NeZero.mk hrnz
    apply Nat.card_le_card_of_injective Units.val Units.ext
  . apply le_of_eq $ Nat.card_zmod r

noncomputable def B : ℕ :=
  ⌊ Real.logb 2 n * Real.sqrt (Nat.card (R n p r hrnz hp hnnoprdivs)) ⌋₊

omit pprime in
lemma B_gt : B n p r hrnz hp hnnoprdivs + 1 > Real.logb 2 n * Real.sqrt (Nat.card (R n p r hrnz hp hnnoprdivs))
  := Nat.lt_floor_add_one (Real.logb 2 ↑n * √↑(Nat.card ↥(R n p r hrnz hp hnnoprdivs)))

omit pprime in
include hn_gt_one in
lemma AgtB : A n r ≥ B n p r hrnz hp hnnoprdivs := by
  unfold A B
  apply Nat.floor_le_floor
  apply (mul_le_mul_left (Real.logb_pos (by norm_num) (Nat.one_lt_cast.mpr hn_gt_one))).mpr
  rw[Real.sqrt_le_sqrt_iff (Nat.cast_nonneg _), Nat.cast_le]
  exact ord_R₂ n p r hrnz hp hnnoprdivs

omit pprime in
include hordern hn_gt_one in
lemma cardRgtB : Nat.card (R n p r hrnz hp hnnoprdivs) > B n p r hrnz hp hnnoprdivs
  := by
  rify

  have annoying : 0 ≤ Real.logb 2 ↑n * √↑(Nat.card ↥(R n p r hrnz hp hnnoprdivs))
   := by
    apply mul_nonneg
    . exact Real.logb_nonneg (by norm_num) (Nat.one_le_cast.mpr (le_of_lt hn_gt_one))
    . exact Real.sqrt_nonneg _

  apply lt_of_le_of_lt (b := Real.logb 2 n * Real.sqrt (Nat.card (R n p r hrnz hp hnnoprdivs)))
  . unfold B
    apply Nat.floor_le
    exact annoying
  apply (sq_lt_sq₀ annoying (Nat.cast_nonneg _)).mp
  rw[mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  nth_rw 2 [sq]
  simp only [Nat.cast_pos, Nat.card_pos, mul_lt_mul_right]
  apply Nat.lt_of_floor_lt (lt_of_lt_of_le hordern (ord_R n p r hrnz hp hnnoprdivs))

include hordern hn_gt_one in
lemma p_gt_B : p > B n p r hrnz hp hnnoprdivs
  := lt_of_lt_of_le (cardRgtB n p r hrnz hp hnnoprdivs hn_gt_one hordern) $ by
    trans r
    . exact ord_R₂ n p r hrnz hp hnnoprdivs
    by_contra h
    exact hnnoprdivs p pprime.out (And.intro hp (le_of_not_ge h))

open Polynomial

noncomputable def prod_factors (T : Finset (Finset.range (B n p r hrnz hp hnnoprdivs + 1)))
  : (ZMod p)[X]
  := ∏ a ∈ T, ((X : (ZMod p)[X]) + C (a.val : ZMod p))

lemma prod_factors_deg (T : Finset (Finset.range (B n p r hrnz hp hnnoprdivs + 1)))
  : (prod_factors n p r hrnz hp hnnoprdivs T).degree = Nat.card T
  := by
  simp only [prod_factors, map_natCast, degree_prod, Nat.card_eq_fintype_card, Fintype.card_coe]
  have : ∀ j ∈ T, ((X : (ZMod p)[X]) + ↑j).degree = 1
    := by intro i hi; compute_degree; exact one_ne_zero
  rw [Finset.sum_congr rfl this]
  exact Eq.symm (Finset.cast_card T)

include hordern hn_gt_one in
lemma deg_of_non_univ (T : Finset (Finset.range (B n p r hrnz hp hnnoprdivs + 1)))
  (hT : T ≠ Finset.univ) : (prod_factors n p r hrnz hp hnnoprdivs T).degree < Nat.card (R n p r hrnz hp hphnnoprdivs)
  := by
  rw[prod_factors_deg n p r hrnz hp hnnoprdivs T]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.cast_lt]
  have := (Finset.card_lt_iff_ne_univ T).mpr hT
  simp only [Finset.mem_range, Fintype.card_coe, Finset.card_range] at this
  calc
    T.card ≤ B n p r hrnz hp hnnoprdivs := Nat.le_of_lt_succ this
    _ < _ := cardRgtB n p r hrnz hp hnnoprdivs hn_gt_one hordern

include hn_gt_one in
lemma prod_factors_in_H (T : Finset (Finset.range (B n p r hrnz hp hnnoprdivs + 1)))
  : AdjoinRoot.mk (f p r) (prod_factors n p r hrnz hp hnnoprdivs T) ∈ H n p r
  := by
  simp[prod_factors]
  apply prod_mem
  intro c hc
  unfold H
  apply Submonoid.subset_closure
  use c
  simp only [α, map_natCast, and_true]
  have : c < B n p r hrnz hp hnnoprdivs + 1 := Finset.mem_range.mp c.property
  have := AgtB n p r hrnz hp hnnoprdivs hn_gt_one
  linarith

include hn_gt_one hordern in
lemma roots_prod_factors (T : Finset (Finset.range (B n p r hrnz hp hnnoprdivs + 1)))
  : ∀ a : ↥ (Finset.range (B n p r hrnz hp hnnoprdivs + 1)),
      a ∈ T ↔ - ↑ a ∈ (prod_factors n p r hrnz hp hnnoprdivs T).roots
  := by
  intro a
  have := λ (i : Finset.range (B n p r hrnz hp hnnoprdivs + 1)) (hI : i ∈ T.val)
    ↦ Polynomial.roots_X_add_C (i : ZMod p)
  simp only [map_one, one_mul, inv_one] at this
  have := λ (i :ZMod p)
    ↦ Polynomial.roots_C_mul_X_add_C i one_ne_zero
  simp only [map_one, one_mul, inv_one] at this
  rw[prod_factors, Polynomial.roots_prod]
  simp_rw[Multiset.mem_bind]
  constructor
  . intro ha
    use a
    simp_rw [this]
    simp_all only [Multiset.mem_singleton, Finset.mem_val, map_natCast, Subtype.forall, Finset.mem_range, roots_X_add_C, implies_true, and_self]

  . intro ⟨b, hb₁, hb₂⟩
    simp_rw [this, Multiset.mem_singleton, neg_inj] at hb₂

    have : a.val = b.val := by
      have hineqa : a < p := lt_of_le_of_lt
        (Nat.le_of_lt_add_one $ Finset.mem_range.mp a.property)
        (p_gt_B n p r hrnz hp hnnoprdivs hn_gt_one hordern)

      have hineqb : b < p := lt_of_le_of_lt
        (Nat.le_of_lt_add_one $ Finset.mem_range.mp b.property)
        (p_gt_B n p r hrnz hp hnnoprdivs hn_gt_one hordern)

      calc
      a.val = ((a : ℕ) : ZMod p).val := (ZMod.val_natCast_of_lt hineqa).symm
      _ = ((b : ℕ) : ZMod p).val := by rw[hb₂]
      _ = b.val := ZMod.val_natCast_of_lt hineqb

    aesop

  rw [Finset.prod_ne_zero_iff]
  intro a ha hpoly
  replace hpoly := congrArg (Polynomial.coeff . 1) hpoly
  simp at hpoly

noncomputable def prod_factors₂ (T : Finset (Finset.range (B n p r hrnz hp hnnoprdivs + 1))) : G n p r hrnz
  := by
  constructor
  rotate_right
  exact Units.mk0 (AdjoinRoot.mk (h p r) (prod_factors n p r hrnz hp hnnoprdivs T)) $ by
    simp [prod_factors, Finset.prod_ne_zero_iff]
    intro a ha haint
    exact nz_of_β_add_x n p r hrnz hp hnnoprdivs hn_gt_one childs_binomial_theorem hordern a $ by
      simp only [Finset.mem_range]
      apply lt_of_lt_of_le ha
      rw [add_le_add_iff_right]
      exact AgtB n p r hrnz hp hnnoprdivs hn_gt_one

  simp [prod_factors, Units.mk0, G]
  apply prod_mem
  intro c hc
  simp only [Gmonoid, Submonoid.mem_map]
  use α p r + c
  constructor
  . apply Submonoid.subset_closure
    simp only [map_natCast, Set.mem_setOf_eq, add_right_inj]
    use c
    simp only [and_true]
    have : c < B n p r hrnz hp hnnoprdivs + 1 := Finset.mem_range.mp c.property
    have := AgtB n p r hrnz hp hnnoprdivs hn_gt_one
    linarith -- almost the same as prod_factors_in_H, maybe could extract it out somehow.

  calc
  _ = φ p r hrnz (α p r) + φ p r hrnz ((c : ZMod p) : AdjoinRoot (f p r)) := map_add _ _ _
  _ = AdjoinRoot.root (h p r) + AdjoinRoot.of (h p r) (c : ZMod p) := by simp only [φ,
    α, AdjoinRoot.algHomOfDvd_apply_root,map_natCast]


noncomputable def prod_factors₃ (T : {x // (x : Finset (Finset.range (B n p r hrnz hp hnnoprdivs + 1))) ≠ Finset.univ})
  : G n p r hrnz := prod_factors₂ n p r hrnz hp hnnoprdivs hn_gt_one childs_binomial_theorem hordern T

include hn_gt_one in
lemma prod_factors₃_injective : Function.Injective (prod_factors₃ n p r hrnz hp hnnoprdivs hn_gt_one childs_binomial_theorem hordern)
  := by
  intro S T hST
  simp only [prod_factors₃, prod_factors₂, Finset.univ_eq_attach, ne_eq] at hST
  replace hxy := congrArg (λ g ↦ g.val) hST
  simp only [Units.mk0_inj] at hxy
  haveI : Fact (n ≥ 1) := Fact.mk (Nat.one_le_of_lt hn_gt_one)
  have := lemma43 n p r hrnz hp hnnoprdivs hn_gt_one childs_binomial_theorem hordern
    (prod_factors n p r hrnz hp hnnoprdivs ↑S)
    (prod_factors n p r hrnz hp hnnoprdivs ↑T)
    (prod_factors_in_H n p r hrnz hp hnnoprdivs hn_gt_one S)
    (prod_factors_in_H n p r hrnz hp hnnoprdivs hn_gt_one T)
    hxy
    (deg_of_non_univ n p r hrnz hp hnnoprdivs hn_gt_one hordern S.val S.property)
    (deg_of_non_univ n p r hrnz hp hnnoprdivs hn_gt_one hordern T.val T.property)

  apply Subtype.eq
  apply Finset.ext
  intro a
  rw [roots_prod_factors, roots_prod_factors, this]
  repeat assumption

include hn_gt_one childs_binomial_theorem hordern in
lemma lower_bound_G : Nat.card (G n p r hrnz) > (n : ℝ)^(Real.sqrt (Nat.card (R n p r hrnz hp hnnoprdivs))) - 1
  := by
    have ineq₁ := calc
      Nat.card (G n p r hrnz) ≥ Nat.card {x // (x : Finset (Finset.range (B _ _ _ _ _ _ + 1))) ≠ Finset.univ} :=
        Nat.card_le_card_of_injective
          (prod_factors₃ _ _ _ _ _ _ _ _ _)
          (prod_factors₃_injective n p r hrnz hp hnnoprdivs hn_gt_one childs_binomial_theorem hordern)
      _ = 2^(B n p r hrnz hp hnnoprdivs + 1) - 1 := by simp -- wow!
    rify at ineq₁
    rw[Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_one] at ineq₁
    suffices : (2 : ℝ)^(B n p r hrnz hp hnnoprdivs + 1) > (n : ℝ)^(Real.sqrt $ Nat.card (R n p r hrnz hp hnnoprdivs))
    . calc
        (Nat.card (G n p r hrnz) : ℝ) ≥ (((2 : ℕ))^(B n p r hrnz hp hnnoprdivs + 1) - 1 : ℝ) := ineq₁
        _ > (n : ℝ)^(Real.sqrt $ Nat.card (R n p r hrnz hp hnnoprdivs)) - 1 := (sub_lt_sub_iff_right 1).mpr this

    apply lt_of_le_of_lt (b := (2 : ℝ) ^ (Real.logb 2 n * Real.sqrt (Nat.card (R n p r hrnz hp hnnoprdivs))))
    . rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (Nat.cast_pos.mpr (by linarith))]
    . simp[B]
      rw[← Real.rpow_natCast]
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      rw [Nat.cast_add, Nat.cast_one]
      exact B_gt n p r hrnz hp hnnoprdivs
