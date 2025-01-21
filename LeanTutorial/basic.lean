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

include hnodd in
lemma n_ne_zero : n ≠ 0 := by
  intro nzero
  rw [nzero] at hnodd
  exact Nat.not_odd_zero hnodd

-- Definitions and basic lemmas that are necessary in many places

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
lemma order_of_X_in_F : orderOf (AdjoinRoot.root (h p r)) = r := by
  have : r > 0 := Nat.zero_lt_of_ne_zero hrnz
  apply (orderOf_eq_iff this).mpr
  constructor
  . have : AdjoinRoot.root (h p r) ^ r - 1 = 0 := by calc
          _ = IsAdjoinRoot.map (AdjoinRoot.isAdjoinRoot _) _ := rfl
          _ = AdjoinRoot.mk (h p r) (X^r-1) := by simp only [this, AdjoinRoot.isAdjoinRoot_map_eq_mk]
          _ = AdjoinRoot.mk (h p r) (f p r) := by congr
          _         = 0 := AdjoinRoot.mk_eq_zero.mpr (h_div p r hrnz)
    have : AdjoinRoot.root (h p r) ^ r - 1 + 1 = 0 + 1 := congrArg (. + 1) this
    simp only [sub_add_cancel, zero_add] at this
    assumption
  . intro m hmltr hmpos eq
    let xm: Polynomial (ZMod p) := X^m -1
    have : h p r ∣ xm := by exact AdjoinRoot.mk_eq_mk.mp eq
    -- h is the root of a cyclotomic polynomial r such that x^m-1 is not a divisor for m < r.
    -- contradiction with [this, hmltr]. Don't know how to show this.
    -- I would like to prove this with help of Alain
    sorry

noncomputable def H : Submonoid (AdjoinRoot (f p r))
  := Submonoid.closure
      {h | ∃ (k : ℕ), k ≤ A n r ∧ h = α _ _ + AdjoinRoot.of (f _ _) (↑ k)}

noncomputable def Gmonoid : Submonoid (𝔽 p r) := Submonoid.map (AdjoinRoot.algHomOfDvd (h_div p r hrnz)) (H n p r)-- what is this homomorphism from and to?
--Remark - this is a type submonoid, but we want a type set tp find a subgroup

include hnodd in
lemma gmonoid_not_contain_zero : 0 ∉ Gmonoid n p r hrnz
  := by
  have gdef : Gmonoid n p r hrnz = Submonoid.map (AdjoinRoot.algHomOfDvd (h_div p r hrnz)) (Submonoid.closure
      {h | ∃ (k : ℕ), k ≤ A n r ∧ h = α _ _ + AdjoinRoot.of (f _ _) (↑ k)}) := rfl
  suffices : ∀ g ∈ Gmonoid n p r hrnz, g ≠ 0
  . intro zeroinG
    exact this 0 zeroinG rfl
  rw [MonoidHom.map_mclosure] at gdef
  simp only [map_natCast] at gdef
  rw[gdef]
  apply Submonoid.closure_induction
  . intro x hx hxzero
    simp at hx
    obtain ⟨y, ⟨a, ha, hb⟩, hy⟩ := hx
    rw [← hy, hb] at hxzero
    simp [α, AdjoinRoot.algHomOfDvd_apply_root] at hxzero
    have idk := calc
      0 = (AdjoinRoot.root (h p r) + ↑ a)^n := by rw[hxzero, zero_pow (n_ne_zero n hnodd)]
      _ = AdjoinRoot.root (h p r)^n + ↑ a := sorry

    have := eq_neg_of_add_eq_zero_right hxzero
    rw [this] at idk
    have := eq_of_add_neg_eq_zero idk.symm
    -- now we need that the order of x in F is r


    sorry
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

def R : Subgroup ((ZMod r)ˣ)
  := Subgroup.closure {
      n' n r hrnz hnnoprdivs,
      p' n p r hrnz hp hnnoprdivs
    }

-- instance : Set.Finite (R n p r hrnz hp hnnoprdivs).carrier := Set.Finite.subset _ _

-- def R' : Finset ((ZMod r)ˣ)
--   := Set.toFinset (R n p r hrnz hp hnnoprdivs).carrier
