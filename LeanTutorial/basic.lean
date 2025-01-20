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
  (hp : p ∣ n) (hnnoprdivs : no_prime_divisors_below n r) (hnnotperfpow : ¬ is_perfect_power n) (hnodd : Odd n) (hnge1 : n > 1)
  (childs_binomial_theorem : ∀ a ∈ Finset.range (A n r + 1),
    (α p r + ↑ a)^n = α p r^n + ↑ a)
  (hordern : orderOf (↑ n : ZMod r) > ⌊(Real.logb 2 n) ^ 2 ⌋₊)

noncomputable def d := orderOf (n : ZMod r)

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

-- our Gmonoid has type submonoid,but it is easier to proof that it is a subgroup if we set it to a type set, but we will work around it for now
def G : Subgroup (𝔽 p r)ˣ where
  carrier := {x | ↑ x ∈ (Gmonoid n p r hrnz)}  -- we would need to prove that all elements in G are nonzero, so we can prove a bijection between g and groupG
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
    g^k = AdjoinRoot.liftHom (f _ _) (α _ _^k) (helper _ _) g
  }

--noncomputable def polH (a : ℤ) : Polynomial ℤ := X + Poly.const a

--lemma fun_in_H (a : ℕ) (eₐ : ℕ) : ∀ g ∈ H, g = ∏₀≤ₐ≤A (X+a) ᵉ := by

-- HOW TO SHOW G IS A GROUP lemma Ggroup (G p r h (h_div p r hrnz) A) : IsSubgroup G := by sorry

noncomputable def φ : Polynomial (ZMod p) →+* AdjoinRoot (f p r) :=
  AdjoinRoot.mk (f p r)

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
  show ∀ g ∈ H n p r, g^n = AdjoinRoot.liftHom _ (α _ _^n) (helper _ _) g
  apply Submonoid.closure_induction
  . intro x ⟨k, hk, hk₂⟩
    rw [hk₂]
    simp only [map_natCast, map_add]
    rw [childs_binomial_theorem _ (Finset.mem_range_succ_iff.mpr hk)]
    congr
    symm
    calc
      _ = (AdjoinRoot.liftHom (f _ _) (α _ _ ^ n) (helper _ _)) (AdjoinRoot.root (f _ _)) := rfl
      _ = α _ _ ^ n := AdjoinRoot.lift_root (helper _ _)
  . simp only [one_pow, map_one]
  . intro x y hx hy hx₂ hy₂
    simp only [map_natCast, map_mul]
    rw [mul_pow,hx₂, hy₂]

include hnge1 in
lemma idkhowtonamethis (a b : ℕ) (ha : a ∈ S n p r) (eqmod : a ≡ b [MOD n^d n r-1])
  : b ∈ S n p r := by
  intro g hg

  have : r ∣ n^d n r - 1 := by
    suffices (n : ZMod r)^d n r - 1 = 0 by
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ r).mp
      rw[← this]
      trans ↑(n^d n r) - 1
      . refine Nat.cast_pred (Nat.pow_pos ?_)
        linarith
      . rw [Nat.cast_pow]
    unfold d
    simp [pow_orderOf_eq_one]
  sorry

lemma how_about_this (a b : ℕ) (ha : a ∣ b) (hb : b ≥ 1) (haineq : a ≥ 3)
  : a.gcd (b-1) = 1 := by
  let c := b/a
  have hc : b = a*c := by exact Eq.symm (Nat.mul_div_cancel' ha)
  have : c ≠ 0 := λ czero ↦ by
    simp_all only [czero,mul_zero,nonpos_iff_eq_zero, one_ne_zero]
  have : c ≥ 1 := Nat.one_le_iff_ne_zero.mpr this
  have : a*(c-1) + a = b := calc
    _ = a * (c - 1 + 1) := by ring
    _ = a * c := by congr; exact Nat.sub_add_cancel this
    _ = b := hc.symm

  have : b-1 = a*(c-1) + a-1 := by congr; exact this.symm
  rw[this]

  have age1 : a ≥ 1 := by linarith

  let a' := a-1
  have ha' : a' + 1 = a := by unfold a'; exact Nat.sub_add_cancel age1
  let a'' := a'-1
  have ha'' : a'' + 1 = a - 1 := by apply Nat.sub_add_cancel; linarith
  calc
  _ = a.gcd ((a * (c - 1) + a - 1) % a) := by rw[← ha', Nat.gcd_add_one, ha', Nat.gcd_comm]
  _ = a.gcd ((a * (c - 1) + (a - 1)) % a) := by rw[Nat.add_sub_assoc age1]
  _ = a.gcd (((a - 1) + a * (c - 1)) % a) := by rw[Nat.add_comm (a * (c-1)) (a-1)]
  _ = a.gcd ((a - 1) % a) := by rw [Nat.add_mul_mod_self_left]
  _ = a.gcd (a - 1) := by congr; exact Nat.self_sub_mod a 1
  _ = (a-1).gcd a := by rw [Nat.gcd_comm]
  _ = (a-1).gcd (a % (a-1)) := by rw[← ha'', Nat.gcd_add_one, ha'', Nat.gcd_comm]
  _ = a'.gcd ((a' + 1) % a') := by unfold a'; rw[ha']
  _ = a'.gcd (1 % a') := by congr 1; exact Nat.add_mod_left _ _
  _ = a'.gcd 1 := by congr; apply Nat.mod_eq_of_lt; linarith
  _ = 1 := by simp only [Nat.gcd_one_right]



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


include hordern hp hnge1 hnodd in
lemma ndivpinS : n/p ∈ S n p r := by
  let k := n^d n r-1
  let a := n * p^(Nat.totient (n^d n r-1) - 1)
  let b := n/p
  have hb : b * p = n := Nat.div_mul_cancel hp

  have hnpowd : 0 < n ^ d n r - 1 := by
    have : 1 < n^d n r := Nat.one_lt_pow (ne_of_lt (Nat.zero_lt_of_lt hordern)).symm hnge1
    exact Nat.zero_lt_sub_of_lt this

  have pkcoprime : Nat.Coprime p k := by
    unfold k
    apply Nat.coprime_iff_gcd_eq_one.mpr
    exact how_about_this p (n ^ d n r)
      (dvd_pow hp (Nat.not_eq_zero_of_lt hordern))
      (one_le_pow₀ (by linarith))
      (pge3 n p hp hnodd)

  have : (a : ZMod k) = b := by
    suffices idk : (a : ZMod k) * p = b * p by
      let pinv := ZMod.inv k p
      have hpinv : p * pinv = 1 := ZMod.coe_mul_inv_eq_one p pkcoprime
      have : ((a : ZMod k) * p) * pinv = (b * p) * pinv := congrArg (. * pinv) idk
      rw [mul_assoc,mul_assoc] at this
      simp only [hpinv, mul_one] at this
      exact this
    unfold a b
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [← Nat.cast_mul (n/p) p, hb, mul_assoc,
      ← Nat.cast_pow, ← Nat.cast_mul (p ^ _) p, ← pow_succ,
      Nat.sub_add_cancel (Nat.totient_pos.mpr hnpowd),
    ]
    have : (p^(k.totient) : ZMod k) = 1 := by
      have : (p^k.totient : ZMod k) = (p : ZMod k)^k.totient := rfl
      have := (ZMod.natCast_eq_natCast_iff (p^k.totient) 1 k).mpr (Nat.ModEq.pow_totient pkcoprime)
      simp only [Nat.cast_pow, Nat.cast_one] at this
      exact this
    simp[this]

  have : ((a : ℤ) : ZMod k) = ((b : ℤ) : ZMod k) := by
    simp only [Int.cast_natCast]
    exact this

  have aequivb_inz : a ≡ b [ZMOD k] := (ZMod.intCast_eq_intCast_iff _ _ _).mp this

  have aequivb : a ≡ b [MOD k] := Int.natCast_modEq_iff.mp aequivb_inz

  have ainS : a ∈ S n p r := sorry
  -- oh, we need lemma41
  -- so we need to restructure stuff so we can depend on that.

  exact idkhowtonamethis n p r hnge1 a b ainS aequivb

def R : ℕ := sorry


--SHOW N IN S NOTES FROM A TALK WITH ALAIN
--submonoid.closure_induction
--small s from thm above is {h | ∃ (k : ℕ), k ≤ A ∧ h = α _ _ + AdjoinRoot.of (f _ _) (↑ k)} (the one from H)
--from Alain's notes: we should think of 1 in g ^ n = 1 as 1 is AdjoinRoot.liftHom (f _ _) (α _ _^k) (helper _ _) g
--define a function p that takes an element of a ring, takes a proof that it is inside of a closure and maps it into a proposition (do not know if it is true or not)
-- we write by, but actually we construct a function
-- refine is similar to apply or exact, but can add ?_ for the stuff we havent proven yet
