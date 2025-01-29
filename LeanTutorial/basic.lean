import Mathlib
open Polynomial

-- these definitions are necessary to state our assumptions
def no_prime_divisors_below (n r : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬(p ∣ n ∧ p ≤ r)

def is_perfect_power (n : ℕ) : Prop :=
  ∃ m p : ℕ, m > 1 ∧ p ≥ 2 ∧ m^p = n

noncomputable def A (n r : ℕ) : ℕ :=
  ⌊Real.logb 2 n * Real.sqrt r⌋₊

noncomputable def f (p r : ℕ) : Polynomial (ZMod p) := X^r - 1
-- the element (X mod f) in Z/p[X]/(f)
noncomputable def α (p r : ℕ): AdjoinRoot (f p r) := AdjoinRoot.root (f _ _)

variable (n p r : ℕ) (hrnz : r ≠ 0) [pprime : Fact (Nat.Prime p)]
  (hp : p ∣ n) (hnnoprdivs : no_prime_divisors_below n r) (hnnotperfpow : ¬ is_perfect_power n) (hnodd : Odd n) (hn_gt_one : n > 1)
  (childs_binomial_theorem : ∀ a ∈ Finset.range (A n r + 1),
    (α p r + ↑ a)^n = α p r^n + ↑ a)
  (hordern : orderOf (↑ n : ZMod r) > ⌊(Real.logb 2 n) ^ 2 ⌋₊)

-- Trivial lemmas (for humans, that is)
include hp hnodd in
lemma pge3 : p ≥ 3 := by
  have pprime : Nat.Prime p := Fact.out
  have h_diff0 : p ≠ 0 := by
    apply Nat.Prime.ne_zero pprime
  have h_diff1 : p ≠ 1 := by
    apply Nat.Prime.ne_one pprime
  have h_diff2 : p ≠ 2 := by
    exact Odd.ne_two_of_dvd_nat hnodd hp
  have hge2 : 2 < p := by
    apply Nat.two_lt_of_ne h_diff0 h_diff1 h_diff2
  simp [ge_iff_le]
  apply Nat.succ_le_of_lt
  trivial

include hn_gt_one in
lemma n_ne_zero : n ≠ 0 :=
  Ne.symm $ ne_of_lt $ calc
    0 < 2 := by norm_num
    _ ≤ n := hn_gt_one

include hn_gt_one in
lemma n_ge_one : n ≥ 1 := by
  exact le_of_lt hn_gt_one

include hn_gt_one in
lemma n_ge_two : n ≥ 2 := hn_gt_one

include hrnz hordern hn_gt_one in
lemma r_ge_two : r ≥ 2 := by
  have rne0 : r ≠ 0 := hrnz
  have rne1 : r ≠ 1 := by
    intro hrone
    have : orderOf (n : ZMod r) ≤ 1 := by
      rw[hrone]
      apply orderOf_le_card_univ
    have ub := lt_of_lt_of_le hordern this
    simp only [Nat.lt_one_iff, Nat.floor_eq_zero, sq_lt_one_iff_abs_lt_one] at ub
    have lb : 1 ≤ Real.logb 2 n := by
      rw[Real.le_logb_iff_rpow_le (by norm_num) (by rw [Nat.cast_pos]; linarith)]
      simp only [Real.rpow_one, Nat.ofNat_le_cast]
      exact hn_gt_one
    have := not_le_of_lt $ lt_of_lt_of_le ub lb
    exact this (le_abs_self _)
  omega

-- Definitions and basic lemmas that are necessary in many places

include hrnz in
lemma f_non_const : (f p r).degree ≠ 0 := by
  have := Polynomial.degree_X_pow_sub_C (Nat.zero_lt_of_ne_zero hrnz) (1 : ZMod p)
  rw [map_one] at this
  unfold f
  rw [this]
  exact Nat.cast_ne_zero.mpr hrnz

instance instNontrivialAdjoinRootF : Nontrivial (AdjoinRoot (f p r))
  := AdjoinRoot.nontrivial (f p r) (f_non_const p r hrnz)

instance instCharPAdjoinRootF: CharP (AdjoinRoot (f p r)) p := by
  haveI := instNontrivialAdjoinRootF p r hrnz
  exact charP_of_injective_algebraMap' (ZMod p) (AdjoinRoot (f p r)) p

noncomputable def d := orderOf (n : ZMod r)

include hordern hn_gt_one in
lemma n_td_d_gt_one : 1 < n^d n r :=
  Nat.one_lt_pow (ne_of_lt (Nat.zero_lt_of_lt hordern)).symm hn_gt_one

noncomputable def h : (ZMod p)[X] := Polynomial.factor (Polynomial.cyclotomic r (ZMod p))
lemma h_irr : Irreducible (h p r) := irreducible_factor (cyclotomic r (ZMod p))
instance h_irreducible : Fact (Irreducible (h p r)) := by
  exact Fact.mk (h_irr _ _)

-- somehow, it doesn't see hrnz if I don't explicitly give it as an argument?
include hrnz in
lemma h_div_cyclotomic : h p r ∣ Polynomial.cyclotomic r (ZMod p) := by
  apply factor_dvd_of_not_isUnit
  refine not_isUnit_of_degree_pos (cyclotomic r (ZMod p)) ?_
  rw [degree_cyclotomic r (ZMod p)]
  apply WithBot.coe_lt_coe.mpr
  simp only [Nat.cast_id, Nat.totient_pos]
  exact Nat.zero_lt_of_ne_zero hrnz

include hrnz in
lemma h_div : h p r ∣ f p r := by
  trans Polynomial.cyclotomic r (ZMod p)
  . exact h_div_cyclotomic p r hrnz
  . exact cyclotomic.dvd_X_pow_sub_one r (ZMod p)

def 𝔽 := AdjoinRoot (h p r)

noncomputable def β : 𝔽 p r
  := AdjoinRoot.root (h p r)

noncomputable instance : Field (𝔽 p r) := by
  unfold 𝔽
  infer_instance

noncomputable instance : Algebra (ZMod p) (𝔽 p r) := by
  unfold 𝔽
  infer_instance

noncomputable instance : Finite (𝔽 p r) := by
  have : Fact (Irreducible (h p r)) := by infer_instance
  have := AdjoinRoot.powerBasis (f := h p r) (Irreducible.ne_zero this.elim)
  haveI : Module.Finite (ZMod p) (𝔽 p r) := PowerBasis.finite this
  have := Module.finite_of_finite (ZMod p) (M := 𝔽 p r)
  infer_instance

lemma prod_subset_dvd
 {α : Type u_3} {β : Type u_4} [CommMonoid β] (s : Finset α) (t : Finset α) (hst : s ⊆ t) (f : α → β) :
  ∏ x ∈ s, f x ∣ ∏ y ∈ t, f y
  := Finset.prod_dvd_prod_of_subset s t f hst

include hrnz hp hnnoprdivs in
lemma order_of_X_in_F : orderOf (β p r) = r := by
  have r_gt_zero : r > 0 := Nat.zero_lt_of_ne_zero hrnz
  apply (orderOf_eq_iff r_gt_zero).mpr
  constructor
  . have : β p r ^ r - 1 = 0 := by calc
          _ = IsAdjoinRoot.map (AdjoinRoot.isAdjoinRoot _) _ := rfl
          _ = AdjoinRoot.mk (h p r) (X^r-1) := by simp only [r_gt_zero, AdjoinRoot.isAdjoinRoot_map_eq_mk]
          _ = AdjoinRoot.mk (h p r) (f p r) := by congr
          _ = 0 := AdjoinRoot.mk_eq_zero.mpr (h_div p r hrnz)
    have : β p r ^ r - 1 + 1 = 0 + 1 := congrArg (. + 1) this
    simp only [sub_add_cancel, zero_add] at this
    assumption
  . intro m hmltr hmpos eq
    have m_dvd_r : m ∣ r := by sorry -- oh.
    have h_dvd_prod_cyclot : h p r ∣ X^m -1 := AdjoinRoot.mk_eq_mk.mp eq
    -- rw[← prod_cyclotomic_eq_X_pow_sub_one hmpos] at h_dvd_prod_cyclot
    have h_dvd_cyclot_r : h p r ∣ Polynomial.cyclotomic r (ZMod p) := h_div_cyclotomic p r hrnz
    have p_ndvd_r : ¬(p ∣ r) := by
      intro p_dvd_r
      have := Nat.le_of_dvd r_gt_zero p_dvd_r
      exact hnnoprdivs p pprime.out (And.intro hp this)
    have xr_sep : Separable (f p r) := by
      have := Polynomial.separable_X_pow_sub_C' p r (1 : ZMod p) p_ndvd_r one_ne_zero
      simp at this
      exact this
    have : h p r * h p r ∣ f p r := by
      unfold f
      rw [← prod_cyclotomic_eq_X_pow_sub_one r_gt_zero]
      calc
      h p r * h p r ∣ cyclotomic r (ZMod p) * (X^m - 1) := mul_dvd_mul h_dvd_cyclot_r h_dvd_prod_cyclot

      _ = cyclotomic r (ZMod p) * ∏ i ∈ Nat.divisors m, cyclotomic i (ZMod p) := by rw[← prod_cyclotomic_eq_X_pow_sub_one hmpos]

      _ = ∏ i ∈ insert r (Nat.divisors m), cyclotomic i (ZMod p) := by
        symm
        apply Finset.prod_insert
        rw[Nat.mem_divisors]
        intro a
        obtain ⟨hdvd, hm⟩ := a
        have := Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hm) hdvd
        have := lt_of_lt_of_le hmltr this
        exact lt_irrefl _ this

      _ ∣ ∏ i ∈ r.divisors, cyclotomic i (ZMod p)
        := Finset.prod_dvd_prod_of_subset _ _ (cyclotomic . (ZMod p)) $ by
          apply Finset.insert_subset
          . simp only [Nat.divisors, Finset.mem_filter, Finset.mem_Ico, lt_add_iff_pos_right,
              zero_lt_one, and_true, dvd_refl]
            exact r_gt_zero
          exact Nat.divisors_subset_of_dvd hrnz m_dvd_r

    have := Polynomial.Separable.squarefree xr_sep (h p r) this

    -- get contradiction
    exact Irreducible.not_unit (h_irr p r) this

    -- proof suggested by alain: f = X^r - 1 is separable because its derivative is rX^(r-1) which is nonzero
    -- at the roots of f (p does not divide r!). Writing X^r-1 = ∏ (d ∣ r) Φd, we see that a root of one cyclotomic
    -- polynomial cannot be a root of any other.

noncomputable def φ : AdjoinRoot (f p r) →ₐ[ZMod p] AdjoinRoot (h p r)
  := AdjoinRoot.algHomOfDvd (h_div p r hrnz)

noncomputable def H : Submonoid (AdjoinRoot (f p r))
  := Submonoid.closure
      {h | ∃ (k : ℕ), k ≤ A n r ∧ h = α _ _ + AdjoinRoot.of (f _ _) (↑ k)}

noncomputable def Gmonoid : Submonoid (𝔽 p r) := Submonoid.map (φ p r hrnz) (H n p r)-- what is this homomorphism from and to?
--Remark - this is a type submonoid, but we want a type set tp find a subgroup

include childs_binomial_theorem hp hnnoprdivs hrnz hordern hn_gt_one in
lemma nz_of_β_add_x : ∀ a ∈ Finset.range (A n r + 1), β p r + ↑ a ≠ 0
  := by
  intro a ha hzero
  have hβ := add_eq_zero_iff_eq_neg.mp hzero
  have := add_eq_zero_iff_eq_neg.mp $ Eq.symm $ calc
    0 = (β p r + ↑ a)^n := by rw[hzero,zero_pow (n_ne_zero n hn_gt_one)]
    _ = φ p r hrnz ((α p r + ↑ a)^n) := by simp[α, φ, β, AdjoinRoot.algHomOfDvd_apply_root (h_div p r hrnz)]
    _ = φ p r hrnz (α p r^n + ↑ a) := by rw [childs_binomial_theorem a ha]
    _ = β p r^n + (↑ a : 𝔽 p r) := by simp[α, φ, β, AdjoinRoot.algHomOfDvd_apply_root (h_div p r hrnz)]
  rw[← hβ] at this

  have βnonzero : β p r ≠ 0 := by
    intro βzero
    have := pow_orderOf_eq_one (β p r)
    rw [order_of_X_in_F n p r hrnz hp hnnoprdivs, βzero, zero_pow hrnz] at this
    apply zero_ne_one this

  rw [← Nat.sub_add_cancel (n_ge_one n hn_gt_one), pow_add, pow_one] at this
  have := mul_left_eq_self₀.mp this
  simp[βnonzero] at this

  have rdivn1 := orderOf_dvd_iff_pow_eq_one.mpr this
  rw [order_of_X_in_F n p r hrnz hp hnnoprdivs] at rdivn1

  have : (n : ZMod r) = 1 := by
    haveI : NeZero r := NeZero.mk hrnz
    refine (ZMod.natCast_eq_iff r n 1).mpr ?_
    obtain ⟨k, hk⟩ := rdivn1
    use k
    rw[← hk,add_comm, ZMod.val_one'' (ne_of_lt (r_ge_two n r hrnz hn_gt_one hordern)).symm, Nat.sub_add_cancel (n_ge_one n hn_gt_one)]

  have : orderOf (n : ZMod r) = 1 := by exact orderOf_eq_one_iff.mpr this
  simp only [this, gt_iff_lt, Nat.lt_one_iff, Nat.floor_eq_zero, sq_lt_one_iff_abs_lt_one] at hordern
  have : Real.logb 2 n < 1 := lt_of_le_of_lt (le_abs_self (Real.logb 2 ↑n)) hordern

  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (Nat.cast_pos'.mpr (n_ge_one n hn_gt_one))] at this
  simp only [Real.rpow_one, Nat.cast_lt_ofNat] at this
  exact not_le_of_lt this hn_gt_one

include childs_binomial_theorem hp hnnoprdivs hn_gt_one hordern in
-- is this even necessary anymore?
lemma gmonoid_not_contain_zero : 0 ∉ Gmonoid n p r hrnz
  := by
  have gdef : Gmonoid n p r hrnz = Submonoid.map (φ p r hrnz) (Submonoid.closure
      {h | ∃ (k : ℕ), k ≤ A n r ∧ h = α _ _ + AdjoinRoot.of (f _ _) (↑ k)}) := rfl
  suffices : ∀ g ∈ Gmonoid n p r hrnz, g ≠ 0
  . intro zeroinG
    exact this 0 zeroinG rfl
  rw [MonoidHom.map_mclosure] at gdef
  simp only [map_natCast] at gdef
  rw[gdef]
  apply Submonoid.closure_induction
  . intro x hx hxzero
    simp only [Set.mem_image, Set.mem_setOf_eq] at hx
    obtain ⟨y, ⟨a, ha, hb⟩, hy⟩ := hx
    rw [← hy, hb] at hxzero
    have : a ∈ Finset.range (A n r + 1) := by
      simp
      exact add_le_add ha (le_refl 1)
    simp [α, β, φ, AdjoinRoot.algHomOfDvd_apply_root, h_div p r hrnz] at hxzero
    exact nz_of_β_add_x n p r hrnz hp hnnoprdivs hn_gt_one childs_binomial_theorem hordern a this hxzero
  . exact one_ne_zero
  . rw[← gdef]
    intro x y _ _ hx hy
    rw[mul_ne_zero_iff]
    tauto



-- our Gmonoid has type submonoid,but it is easier to proof that it is a subgroup if we set it to a type set, but we will work around it for now
def G : Subgroup (𝔽 p r)ˣ where
  carrier := {x | ↑ x ∈ Gmonoid n p r hrnz}  -- we would need to prove that all elements in G are nonzero, so we can prove a bijection between g and groupG
  mul_mem' := by
    rintro k j ok oj -- use g has type submonoid
    simp at ok oj ⊢
    exact Submonoid.mul_mem (Gmonoid n p r hrnz) ok oj
  one_mem' := by
    simp
    exact Submonoid.one_mem (Gmonoid n p r hrnz)
  inv_mem' := by
    rintro u t
    have hu : IsOfFinOrder u := by
      exact isOfFinOrder_of_finite u
    have w := IsOfFinOrder.val_inv_unit hu
    simp at w
    rw[w]
    apply Submonoid.pow_mem
    exact t
    -- G is a finite subset, so any x to some power must be 1

--IsOfFinOrder.val_inv_unit
-- for report an alternative way to do it is to change G to be a subset and then prove a monoid and stuff
-- to proven in S

-- Show that f(X^k) = 0, needed for the definition of S (for evaluation of f at X^k to be well-defined)
lemma helper : aeval (AdjoinRoot.root (f p r) ^ k) (f p r) = 0 := by
  let f' : Polynomial (ZMod p) := f p r
  let α' := AdjoinRoot.root f'
  show (aeval (α' ^ k)) f' = 0
  have : (aeval (α' ^ k)) f' = (α' ^ k) ^ r - 1 := by
    unfold f'
    unfold f
    simp only [map_sub, AdjoinRoot.mk_X, map_pow, aeval_X, map_one]

  rw [this, ← pow_mul, mul_comm k r, pow_mul]

  have : α' ^ r = 1 := by
    have : α' ^ r - 1 = 0 := by calc
      α' ^ r - 1 = IsAdjoinRoot.map (AdjoinRoot.isAdjoinRoot f') f' := rfl
      _         = 0 := by simp only [this, AdjoinRoot.isAdjoinRoot_map_eq_mk, AdjoinRoot.mk_self]
    have : α' ^ r - 1 + 1 = 0 + 1 := congrArg (. + 1) this
    simp only [sub_add_cancel, zero_add] at this
    assumption
  simp [this]

def S : Set ℕ := {
  k | ∀ g ∈ H n p r,
    g^k = g.liftHom (f _ _) (α _ _^k) (helper _ _)
  }

omit [Fact (Nat.Prime p)] in
lemma mk_C_eq_of : (AdjoinRoot.mk (f p r)).comp C = AdjoinRoot.of (f p r)
  := RingHom.ext AdjoinRoot.mk_C

lemma pinS : p ∈ S n p r := by
  intro g hg
  have ⟨q, hq⟩ := AdjoinRoot.mk_surjective g
  rw [← hq]
  simp only [AdjoinRoot.liftHom_mk]
  have : q ^ p = q.eval₂ C (X^p) := by
    rw [← Polynomial.expand_char, ZMod.frobenius_zmod]
    simp
    rfl

  calc
  _ = AdjoinRoot.mk (f _ _) (q.eval₂ C (X^p)):= by rw[← this]; rfl
  _ = q.eval₂ ((AdjoinRoot.mk (f _ _)).comp C) (AdjoinRoot.mk (f _ _) (X^p)) := Polynomial.hom_eval₂ _ _ _ _
  _ = q.eval₂ (AdjoinRoot.of (f _ _)) (AdjoinRoot.root (f _ _)^p) := by simp only [mk_C_eq_of, map_pow, AdjoinRoot.mk_X]
  _ = _ := rfl

include childs_binomial_theorem in
lemma ninS : n ∈ S n p r := by
  show ∀ g ∈ H n p r, g^n = g.liftHom _ (α _ _^n) (helper _ _)
  apply Submonoid.closure_induction
  . intro x ⟨k, hk, hk₂⟩
    rw [hk₂]
    simp only [map_natCast, map_add]
    rw [childs_binomial_theorem _ (Finset.mem_range_succ_iff.mpr hk)]
    congr
    symm
    calc
      _ = (AdjoinRoot.root (f _ _)).liftHom (f _ _) (α _ _ ^ n) (helper _ _)  := rfl
      _ = α _ _ ^ n := AdjoinRoot.lift_root (helper _ _)
  . simp only [one_pow, map_one]
  . intro x y hx hy hx₂ hy₂
    simp only [map_natCast, map_mul]
    rw [mul_pow,hx₂, hy₂]

-- TODO: cleanup + maybe change definition of S??
-- although the way it's stated here is how I prefer to think of it.
lemma restatement_S (k : ℕ)
  : k ∈ S n p r ↔ ∀ g : (ZMod p)[X], AdjoinRoot.mk (f p r) g ∈ H n p r → AdjoinRoot.mk (f p r) (g.comp (X^k)) = AdjoinRoot.mk (f p r) (g^k)
  := by
  constructor
  . intro hk g hg
    unfold comp
    rw[map_pow,hom_eval₂,mk_C_eq_of]
    symm
    calc
    (AdjoinRoot.mk (f p r)) g ^ k = (AdjoinRoot.mk (f p r) g).liftHom (f _ _) (α _ _^k) (helper _ _) := hk _ hg
    _ = g.aeval (α _ _^k) := by exact rfl
    _ = _ := by simp[aeval, α]; congr
  . intro hk q
    refine AdjoinRoot.induction_on (f p r) q ?_
    intro s hs
    unfold α
    have := hk s hs
    rw [map_pow] at this
    rw[← this, AdjoinRoot.liftHom_mk]
    unfold comp
    rw[hom_eval₂, map_pow, AdjoinRoot.mk_X, mk_C_eq_of]
    unfold aeval eval₂AlgHom' Algebra.ofId
    simp

lemma restatement_S₂ (k : ℕ)
  : k ∈ S n p r ↔ ∀ g : (ZMod p)[X], AdjoinRoot.mk (f p r) g ∈ H n p r → g.aeval (α p r^k) = AdjoinRoot.mk (f p r) g^k
  := by
  rw[restatement_S]
  have : ∀ g : (ZMod p)[X], (AdjoinRoot.mk (f p r)) (g.comp (X ^ k)) = g.aeval (α p r^k) := by
    simp[comp, α, hom_eval₂, mk_C_eq_of, aeval, Algebra.ofId]
  simp_rw[this]
  rfl

-- lemma helper₂ : (h p r).aeval (β p r ^ k) = 0 := by
--   simp only [aeval, eval₂AlgHom'_apply]
--   sorry

lemma algHomOfDvd_mk (K : Type*) [Field K] {p q : K[X]} (hpq : q ∣ p)
  {g : K[X]}
  : AdjoinRoot.algHomOfDvd hpq (AdjoinRoot.mk p g) = AdjoinRoot.mk q g
  := by
  induction g using Polynomial.induction_on' with
  | h_add g g' hg hg' => simp[hg, hg']
  | h_monomial k a =>
    rw[← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, AdjoinRoot.mk_C, map_pow, map_mul, AdjoinRoot.mk_X,AdjoinRoot.algHomOfDvd_apply_root hpq]
    congr 1
    unfold AdjoinRoot.algHomOfDvd
    simp

include hrnz in
lemma consequence_S
  (k : ℕ) (hk : k ∈ S n p r)
  (g : (ZMod p)[X])
  (hg : AdjoinRoot.mk (f p r) g ∈ H n p r)
  : g.aeval (β p r^k) = AdjoinRoot.mk (h p r) g^k
  := by
  let a := AdjoinRoot.mk (f p r) g
  have ha : a ∈ H n p r := hg
  have := congrArg (φ p r hrnz) (hk a ha)
  rw [map_pow] at this
  have what : φ p r hrnz a = (AdjoinRoot.mk (h p r)) g := by
    simp[φ, a, algHomOfDvd_mk]
  rw [what] at this
  rw[this]
  unfold β α φ a
  rw[AdjoinRoot.liftHom_mk,← Polynomial.aeval_algHom_apply, map_pow, AdjoinRoot.algHomOfDvd_apply_root]
  rfl

include hrnz hnnoprdivs in
lemma n_coprime_r : n.Coprime r := by
  apply Nat.coprime_of_dvd
  intro k hk hkdivn hkdivr
  have : k ≤ r := Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hrnz) hkdivr
  exact hnnoprdivs _ hk (And.intro hkdivn this)

include n hrnz hnnoprdivs hp in
omit [Fact (Nat.Prime p)] in
lemma p_coprime_r : p.Coprime r := Nat.Coprime.coprime_dvd_left hp (n_coprime_r n r hrnz hnnoprdivs)

def n' := ZMod.unitOfCoprime n (n_coprime_r n r hrnz hnnoprdivs)
def p' := ZMod.unitOfCoprime p (p_coprime_r n _ _ hrnz hp hnnoprdivs)
def n_over_p' := n' n r hrnz hnnoprdivs / p' n p r hrnz hp hnnoprdivs

def R : Subgroup ((ZMod r)ˣ)
  := Subgroup.closure {
      n' n r hrnz hnnoprdivs,
      p' n p r hrnz hp hnnoprdivs
    }

noncomputable instance instRFintype : Fintype ↑(R n p r hrnz hp hnnoprdivs : Set (ZMod r)ˣ)
  := Fintype.ofFinite ↑↑(R n p r hrnz hp hnnoprdivs)
