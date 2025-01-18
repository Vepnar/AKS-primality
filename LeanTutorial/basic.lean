import Mathlib
open Polynomial

-- these definitions are necessary to state our assumptions
def no_prime_divisors_below (n r : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬(p ∣ n ∧ p ≤ r)

def is_perfect_power (n : ℕ) : Prop :=
  ∃ m p : ℕ, m > 1 ∧ p ≥ 2 ∧ m^p = n

noncomputable def A (n r : ℕ) : ℕ :=
  Nat.floor (Real.logb 2 n* Real.sqrt r)

noncomputable def f (p r : ℕ) : Polynomial (ZMod p) := X^r - 1
-- the element (X mod f) in Z/p[X]/(f)
noncomputable def α (p r : ℕ): AdjoinRoot (f p r) := AdjoinRoot.root (f _ _)

variable (n p r : ℕ) (hrnz : r ≠ 0) [Fact (Nat.Prime p)]
  (hp : p ∣ n) (hn : no_prime_divisors_below n r) (hhn : ¬ is_perfect_power n) (hhhn : Odd n)
  (childs_binomial_theorem : ∀ a ∈ Finset.range (A n r + 1),
    (α p r + ↑ a)^n = α p r^n + ↑ a)

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
    have : h p r ∣ X^m-1 := sorry -- use AdjoinRoot.mk_eq_zero
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

  have (q : (ZMod p)[X]) : q ^ p = q.comp (X ^ p) := by
    rw [← Polynomial.expand_char, ZMod.frobenius_zmod]
    simp
    exact Polynomial.expand_eq_comp_X_pow p

  have := fun q => congrArg (φ p r) (this q)
  unfold φ at this
  simp at this
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective g

  have := this q

  rw [hq] at this
  rw[this]

  calc
  _ = (AdjoinRoot.mk (f p r)) (q.eval₂ C (X ^ p)) := by rfl
  _ = (AdjoinRoot.mk (f p r)) (q.eval₂ C (X ^ p)) := by rfl
  _ = (AdjoinRoot.liftHom (f p r) (AdjoinRoot.root (f _ _) ^ p) (helper _ _)) g := by sorry
  _ = (AdjoinRoot.liftHom (f p r) (AdjoinRoot.root (f _ _) ^ p) (helper _ _)) g := by rfl
  _ = _ := by rfl

include childs_binomial_theorem in
lemma ninS : n ∈ S n p r := by
  show ∀ g ∈ H n p r, g^n = AdjoinRoot.liftHom _ (α p r^n) (helper _ _) g
  apply Submonoid.closure_induction
  . intro x ⟨k, hk, hk₂⟩
    rw [hk₂]
    simp only [map_natCast, map_add]
    rw [childs_binomial_theorem _ (Finset.mem_range_succ_iff.mpr hk)]
    congr
    symm
    calc
      _ = (AdjoinRoot.liftHom (f p r) (α p r ^ n) (helper _ _)) (AdjoinRoot.root (f p r)) := rfl
      _ = α p r ^ n := AdjoinRoot.lift_root (helper _ _)
  . simp only [one_pow, map_one]
  . intro x y hx hy hx₂ hy₂
    simp only [map_natCast, map_mul]
    rw [mul_pow,hx₂, hy₂]

def R : ℕ := sorry


--SHOW N IN S NOTES FROM A TALK WITH ALAIN
--submonoid.closure_induction
--small s from thm above is {h | ∃ (k : ℕ), k ≤ A ∧ h = α _ _ + AdjoinRoot.of (f _ _) (↑ k)} (the one from H)
--from Alain's notes: we should think of 1 in g ^ n = 1 as 1 is AdjoinRoot.liftHom (f _ _) (α _ _^k) (helper _ _) g
--define a function p that takes an element of a ring, takes a proof that it is inside of a closure and maps it into a proposition (do not know if it is true or not)
-- we write by, but actually we construct a function
-- refine is similar to apply or exact, but can add ?_ for the stuff we havent proven yet
