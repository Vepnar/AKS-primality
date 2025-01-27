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

variable (n p r : ℕ) (hrnz : r ≠ 0) [Fact (Nat.Prime p)]
  (hp : p ∣ n) (hnnoprdivs : no_prime_divisors_below n r) (hnnotperfpow : ¬ is_perfect_power n) (hnodd : Odd n) (hn_gt_one : n > 1)
  (childs_binomial_theorem : ∀ a ∈ Finset.range (A n r + 1),
    (α p r + ↑ a)^n = α p r^n + ↑ a)
  (hordern : orderOf (↑ n : ZMod r) > ⌊(Real.logb 2 n) ^ 2 ⌋₊)

-- Trivial lemmas (for humans, that is)
include hp hnodd in
lemma pge3 : p ≥ 3 := by
  have pprime : Nat.Prime p := Fact.out
  have p_odd : Odd p := by
    exact Odd.of_dvd_nat hnodd hp
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

include hrnz hordern in
lemma r_ge_two : r ≥ 2 := by
  have rne0 : r ≠ 0 := hrnz
  have rne1 : r ≠ 1 := by
    sorry -- annoying
  by_contra hx
  have := lt_of_not_ge hx
  cases r with
  | zero => exact rne0 rfl
  | succ r' => cases r' with
    | zero => exact rne1 rfl
    | succ r'' =>
      rw[add_assoc] at this;
      simp only [Nat.reduceAdd, add_lt_iff_neg_right, not_lt_zero'] at this;

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

include hrnz in
lemma order_of_X_in_F : orderOf (β p r) = r := by
  have : r > 0 := Nat.zero_lt_of_ne_zero hrnz
  apply (orderOf_eq_iff this).mpr
  constructor
  . have : β p r ^ r - 1 = 0 := by calc
          _ = IsAdjoinRoot.map (AdjoinRoot.isAdjoinRoot _) _ := rfl
          _ = AdjoinRoot.mk (h p r) (X^r-1) := by simp only [this, AdjoinRoot.isAdjoinRoot_map_eq_mk]
          _ = AdjoinRoot.mk (h p r) (f p r) := by congr
          _ = 0 := AdjoinRoot.mk_eq_zero.mpr (h_div p r hrnz)
    have : β p r ^ r - 1 + 1 = 0 + 1 := congrArg (. + 1) this
    simp only [sub_add_cancel, zero_add] at this
    assumption
  . intro m hmltr hmpos eq
    let xm: Polynomial (ZMod p) := X^m -1
    have : h p r ∣ xm := by exact AdjoinRoot.mk_eq_mk.mp eq
    -- h is the root of a cyclotomic polynomial r such that x^m-1 is not a divisor for m < r.
    -- contradiction with [this, hmltr]. Don't know how to show this.
    -- I would like to prove this with help of Alain
    sorry
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

include childs_binomial_theorem hrnz hordern hn_gt_one in
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
    rw [order_of_X_in_F p r hrnz, βzero, zero_pow hrnz] at this
    apply zero_ne_one this

  rw [← Nat.sub_add_cancel (n_ge_one n hn_gt_one), pow_add, pow_one] at this
  have := mul_left_eq_self₀.mp this
  simp[βnonzero] at this

  have rdivn1 := orderOf_dvd_iff_pow_eq_one.mpr this
  rw [order_of_X_in_F p r hrnz] at rdivn1

  have : (n : ZMod r) = 1 := by
    haveI : NeZero r := NeZero.mk hrnz
    refine (ZMod.natCast_eq_iff r n 1).mpr ?_
    obtain ⟨k, hk⟩ := rdivn1
    use k
    rw[← hk,add_comm, ZMod.val_one'' (ne_of_lt (r_ge_two n r hrnz hordern)).symm, Nat.sub_add_cancel (n_ge_one n hn_gt_one)]

  have : orderOf (n : ZMod r) = 1 := by exact orderOf_eq_one_iff.mpr this
  simp only [this, gt_iff_lt, Nat.lt_one_iff, Nat.floor_eq_zero, sq_lt_one_iff_abs_lt_one] at hordern
  have : Real.logb 2 n < 1 := lt_of_le_of_lt (le_abs_self (Real.logb 2 ↑n)) hordern

  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (Nat.cast_pos'.mpr (n_ge_one n hn_gt_one))] at this
  simp only [Real.rpow_one, Nat.cast_lt_ofNat] at this
  exact not_le_of_lt this hn_gt_one

include childs_binomial_theorem hn_gt_one hordern in
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
    exact nz_of_β_add_x n p r hrnz hn_gt_one childs_binomial_theorem hordern a this hxzero
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

--noncomputable def polH (a : ℤ) : Polynomial ℤ := X + Poly.const a

--lemma fun_in_H (a : ℕ) (eₐ : ℕ) : ∀ g ∈ H, g = ∏₀≤ₐ≤A (X+a) ᵉ := by

-- HOW TO SHOW G IS A GROUP lemma Ggroup (G p r h (h_div p r hrnz) A) : IsSubgroup G := by sorry

lemma pinS : p ∈ S n p r := by
  intro g hg
  have ⟨q, hq⟩ := AdjoinRoot.mk_surjective g
  rw [← hq]
  simp only [AdjoinRoot.liftHom_mk]
  have : q ^ p = q.eval₂ C (X^p) := by
    rw [← Polynomial.expand_char, ZMod.frobenius_zmod]
    simp
    rfl

  have idk : (AdjoinRoot.mk (f p r)).comp C = AdjoinRoot.of (f p r)
  := RingHom.ext AdjoinRoot.mk_C

  calc
  _ = AdjoinRoot.mk (f _ _) (q.eval₂ C (X^p)):= by rw[← this]; rfl
  _ = q.eval₂ ((AdjoinRoot.mk (f _ _)).comp C) (AdjoinRoot.mk (f _ _) (X^p)) := Polynomial.hom_eval₂ _ _ _ _
  _ = q.eval₂ (AdjoinRoot.of (f _ _)) (AdjoinRoot.root (f _ _)^p) := by simp only [idk,map_pow, AdjoinRoot.mk_X]
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
