import Mathlib
open Polynomial

variable (p r : ℕ) (hrnz : r ≠ 0) [Fact (Nat.Prime p)] (A : ℕ)

noncomputable def h : (ZMod p)[X] := Polynomial.factor (Polynomial.cyclotomic r (ZMod p))
lemma h_irr : Irreducible (h p r) := irreducible_factor (cyclotomic r (ZMod p))
instance h_irreducible : Fact (Irreducible (h p r)) := by
  exact Fact.mk (h_irr _ _)

-- somehow, it doesn't see hrnz if I don't explicitly give it as an argument?
lemma h_div_cyclotomic (hrnz : r ≠ 0) : h p r ∣ Polynomial.cyclotomic r (ZMod p) := by
  apply factor_dvd_of_not_isUnit
  refine not_isUnit_of_degree_pos (cyclotomic r (ZMod p)) ?_
  rw [degree_cyclotomic r (ZMod p)]
  apply WithBot.coe_lt_coe.mpr
  simp only [Nat.cast_id, Nat.totient_pos]
  exact Nat.zero_lt_of_ne_zero hrnz

lemma h_div (hrnz : r ≠ 0) : h p r ∣ X^r-1 := by
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

noncomputable def f : Polynomial (ZMod p) := X^r - 1

noncomputable def α : AdjoinRoot (f p r) := AdjoinRoot.root (f _ _)

noncomputable def H : Submonoid (AdjoinRoot (f p r))
  := Submonoid.closure
      {h | ∃ (k : ℕ), k ≤ A ∧ h = α _ _ + AdjoinRoot.of (f _ _) (↑ k)}

noncomputable def Gmonoid : Submonoid (𝔽 p r) := Submonoid.map (AdjoinRoot.algHomOfDvd (h_div p r hrnz)) (H p r A)-- what is this homomorphism from and to?
--Remark - this is a type submonoid, but we want a type set tp find a subgroup

-- our Gmonoid has type submonoid,but it is easier to proof that it is a subgroup if we set it to a type set, but we will work around it for now
def G : Subgroup (𝔽 p r)ˣ where
  carrier := {x | ↑ x ∈ (Gmonoid p r hrnz A)}  -- we would need to prove that all elements in G are nonzero, so we can prove a bijection between g and groupG
  mul_mem' := by
    rintro k j ok oj -- use g has type submonoid
    simp at ok oj ⊢
    exact Submonoid.mul_mem (Gmonoid p r hrnz A) ok oj
  one_mem' := by
    simp
    exact Submonoid.one_mem (Gmonoid p r hrnz A)
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
  k | ∀ g ∈ H p r A,
    g^k = AdjoinRoot.liftHom (f _ _) (α _ _^k) (helper _ _) g
  }

example : ℤ →+* (ZMod p) := by exact Int.castRingHom (ZMod p)


#check Int.castRingHom (ZMod 3)

#check H

lemma lemma41 (a b : ℕ)
  (sha : a ∈ S p r A)  -- make the variables explicit --> ()
  (shb : b ∈ S p r A)
  : a*b ∈ S p r A := by
  show ∀ g ∈ H p r A,
    g^(a*b) = AdjoinRoot.liftHom (f p r) (α p r^(a*b)) (helper p r) g

  intro g hg
  rw [pow_mul, sha, shb]

  -- ugly part to make sure sha and shb actually apply
  -- ASK ALAIN
  rotate_right 1
  trivial

  rotate_right 1
  rw [← sha]
  apply pow_mem
  trivial
  trivial

  -- proof of what we actually care about
  let φ := (AdjoinRoot.liftHom (f _ _) (α _ _ ^ b) (helper p r)).comp (AdjoinRoot.liftHom (f _ _) (α _ _ ^ a) (helper _ _))
  let ψ := (AdjoinRoot.liftHom (f _ _) (α _ _ ^ (a * b)) (helper p r))

  have : φ = ψ := AdjoinRoot.algHom_ext (by calc
    _ = (AdjoinRoot.liftHom (f _ _) (α _ _ ^ b) (helper _ _)) (AdjoinRoot.liftHom (f _ _) (α _ _ ^ a) (helper p r) (AdjoinRoot.root (f _ _))) := rfl
    _ = (AdjoinRoot.liftHom (f _ _) (α _ _ ^ b) (helper _ _)) (α _ _^a) := by (rw[AdjoinRoot.liftHom_root (a := α _ _ ^ a) ]; )
    _ = (AdjoinRoot.liftHom (f _ _) (α _ _ ^ b) (helper _ _) (α _ _))^a := by (simp[AdjoinRoot.liftHom_root]; )
    _ = (AdjoinRoot.liftHom (f _ _) (α _ _ ^ b) (helper _ _) (AdjoinRoot.root (f _ _)))^a := rfl
    _ = (α _ _ ^ b)^a := by rw[AdjoinRoot.liftHom_root]
    _ = α _ _^(b*a) := by simp[pow_mul]
    _ = α _ _^(a*b) := by simp[mul_comm]
    _ = (AdjoinRoot.liftHom (f _ _) (α _ _ ^ (a * b)) (helper _ _)) (AdjoinRoot.root _) := by simp only [AdjoinRoot.liftHom_root]
    _ = ψ (AdjoinRoot.root (f _ _)) := rfl
    )

  calc
    _ = φ g := rfl
    _ = ψ g := by rw [this]
    _ = _ := rfl

lemma lemma42 (a b : ℕ)
  (hineq : a ≥ b)
  (ha : a ∈ S p r A)
  (hb : b ∈ S p r A)
  (hab : a ≡ b [MOD r]) :
  a ≡ b [MOD Nat.card (G p r hrnz A)] := by

  -- part one: for all polys g ∈ ℤ/p[x][x], x^r-1 ∣ g(x^a) - g(x^b)

  have part1 : ∀ g : Polynomial (Polynomial (ZMod p)), AdjoinRoot.mk (f p r) (g.eval (X^a)) = AdjoinRoot.mk (f p r) (g.eval (X^b)) := by
    intro g

    let ab : Polynomial (ZMod p) := X^(a-b)-1
    have f_dvd_ab : (f p r) ∣ ab := by
      let k := (a - b)/r
      have : r ∣ a-b := (Nat.modEq_iff_dvd' hineq).mp (Nat.ModEq.symm hab)
      have : r * k = (a-b) := Nat.mul_div_cancel' this
      unfold ab
      rw [←this]
      have := sub_dvd_pow_sub_pow (X^r : Polynomial (ZMod p)) 1 k
      rw [one_pow, ← pow_mul] at this
      exact this

    let xaxb : Polynomial (ZMod p) := X^a - X^b
    have ab_dvd_xaxb : ab ∣ xaxb := by
      constructor -- what does this do
      rotate_left 1 -- what does this do
      . exact X^b
      . ring_nf
        rw [← pow_add, add_comm b (a-b), Nat.sub_add_cancel hineq]
        ring

    have xaxb_dvd_gxagxb : xaxb ∣ g.eval (X^a) - g.eval (X^b)
      := sub_dvd_eval_sub (X^a) (X^b) g

    have : (f p r) ∣ g.eval (X^a) - g.eval (X^b)
      := dvd_trans (dvd_trans f_dvd_ab ab_dvd_xaxb) xaxb_dvd_gxagxb

    exact eq_of_sub_eq_zero (AdjoinRoot.mk_eq_zero.mpr this)

  -- part 2: applying this to elements of H
  have part2 : ∀ g ∈ H p r A, g^a = g^b := by
    intro g hg
    -- ASK ALAIN
    rw [ha, hb] <;> try assumption

    have : α p r ^ a = α p r ^ b := calc
      _ = AdjoinRoot.mk (f p r) (X^a) := by rfl
      _ = AdjoinRoot.mk (f p r) ((X : Polynomial (Polynomial (ZMod p))).eval (X^a)) := by rw [eval_X]
      _ = AdjoinRoot.mk (f p r) ((X : Polynomial (Polynomial (ZMod p))).eval (X^b)) := part1 X
      _ = AdjoinRoot.mk (f p r) (X^b) := by rw[eval_X (x := X^b)]
      _ = _ := by rfl

    simp only [this]

  have : ∀ g ∈ H p r A, (AdjoinRoot.algHomOfDvd (h_div p r hrnz) g)^a = (AdjoinRoot.algHomOfDvd (h_div p r hrnz) g)^b
    := λ g hg ↦ calc
    _ = AdjoinRoot.algHomOfDvd (h_div p r hrnz) (g^a) := by simp only [map_pow]
    _ = AdjoinRoot.algHomOfDvd (h_div p r hrnz) (g^b) := by rw[part2]; assumption
    _ = (AdjoinRoot.algHomOfDvd (h_div p r hrnz) g)^b := by simp only [map_pow]

  have hidk : ∀ g ∈ G p r hrnz A, g^a = g^b := λ g ⟨q, hq, hqg⟩ ↦ by
    have := this q hq
    have := (calc
    (rfl.mp (↑ g : 𝔽 p r))^a = (AdjoinRoot.algHomOfDvd (h_div p r hrnz) q)^a := by rw[← hqg]; rfl
    _ = (AdjoinRoot.algHomOfDvd (h_div p r hrnz) q)^b := this
    _ = (rfl.mp (↑ g : 𝔽 p r))^b := by rw[← hqg]; rfl)

    exact Units.eq_iff.mp this

  have : ∀ g ∈ G p r hrnz A, g^(a-b) = 1 := λ g ⟨q, hq, hqg⟩ ↦ by
    -- let g' : G p r h (h_div p r hrnz) A := ⟨g, ⟨q,hq,hqg⟩⟩
    haveI : IsRightCancelMul (G p r hrnz A) := by
      infer_instance

    have : g^a = g^b := hidk g ⟨q, hq, hqg⟩
    have : g^(a-b) * g^b = 1 * g^b := by
      rw [pow_sub_mul_pow (h := hineq), one_mul, this]

    have : g^(a-b) = 1 := by
      refine pow_eq_one_iff_modEq.mpr ?_
      --show ∃ c, ↑(orderOf g) * c = ↑a - ↑b := by
      --show a ≡ b [MOD orderOf g]
      rw[Nat.modEq_zero_iff_dvd]
      rw[orderOf_dvd_iff_pow_eq_one]
      exact
  have : ∀ g ∈ G p r hrnz A, orderOf g ∣ a-b := by --substituting names for variables, here for a-b?
    intro g1
    intro g2
    rw[orderOf_dvd_iff_pow_eq_one]
    sorry

    -- exact fun g a_1 ↦ orderOf_dvd_of_pow_eq_one (this g a_1) This is a shorter version but i wanted to understand it fully


    -- have : g'^(a-b) * g'^b = 1 * g'^b := by
    --   simp

    -- have hidk : g'^(a-b) = 1 := mul_right_cancel (a := g'^(a-b)) (G := G p r h (h_div p r hrnz) A) this
    -- have hidk2 : ↑ g'^(a-b) = (↑ 1 : 𝔽 p r) := by
    --   exact congrArg (coe) hidk
    -- have : (↑ (g'^(a-b)) : 𝔽 p r) = g^(a-b) := rfl

  sorry

def no_prime_divisors (n : ℕ) (r : ℕ): Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬(p ∣ n ∧ p ≤ r)

def isPerfectPower (n : ℤ) (p : ℕ): Prop :=
  ∃ m : ℤ, m > 1 ∧ p ≥ 2 ∧ m^p = n

--noncomputable def polH (a : ℤ ) : Polynomial ℤ := X + Poly.const a

--lemma fun_in_H (a : ℕ ) (eₐ : ℕ ) : ∀ g ∈ H, g = ∏₀≤ₐ≤A (X+a) ᵉ := by

-- HOW TO SHOW G IS A GROUP lemma Ggroup (G p r h (h_div p r hrnz) A) : IsSubgroup G := by sorry

noncomputable def φ : Polynomial (ZMod p) →+* AdjoinRoot (f p r) :=
  AdjoinRoot.mk (f p r)

  lemma pinS : p ∈ S p r A := by
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

  lemma ninS (n r : ℕ ) (hp : p ∣ n) (hn : no_prime_divisors n r) (hhn : ¬ isPerfectPower n p) (hhhn : Odd n) : n ∈ S p r A := by
  show ∀ g ∈ H p r A, g^n = AdjoinRoot.liftHom _ (α p r^n) (helper _ _) g
  intro g hg
  rw[dvd_def] at hp
  cases' hp with c hp
  rw[hp]
  rw[pow_mul]
  sorry

def R : ℕ := sorry

lemma lemma43 (g q : Polynomial (ZMod p)) (hg : AdjoinRoot.mk h g ∈ Gmonoid p r h (h_div p r hrnz) A) (hq : AdjoinRoot.mk h q ∈ Gmonoid p r h (h_div p r hrnz) A)
  (hmod : AdjoinRoot.mk h g = AdjoinRoot.mk h q)
  (hdegg : Polynomial.degree g < R) (hdegq : Polynomial.degree q < R)
  : g = q := by
  let Δ := g - q
  have hΔmod : ∀ k ∈ S p r A, AdjoinRoot.mk h (Δ.comp X^k) = 0
  intro X




  --rw [hmod, AdjoinRoot.mk_sub],
  --exact sub_self _, modular equality??

--SHOW N IN S NOTES FROM A TALK WITH ALAIN
--submonoid.closure_induction
--small s from thm above is {h | ∃ (k : ℕ), k ≤ A ∧ h = α _ _ + AdjoinRoot.of (f _ _) (↑ k)} (the one from H)
--from Alain's notes: we should think of 1 in g ^ n = 1 as 1 is AdjoinRoot.liftHom (f _ _) (α _ _^k) (helper _ _) g
--define a function p that takes an element of a ring, takes a proof that it is inside of a closure and maps it into a proposition (do not know if it is true or not)
-- we write by, but actually we construct a function
-- refine is similar to apply or exact, but can add ?_ for the stuff we havent proven yet
