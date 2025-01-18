import Mathlib
import LeanTutorial.basic
-- import LeanTutorial.lemma_41

open Polynomial
variable (p r : ℕ) (hrnz : r ≠ 0) [Fact (Nat.Prime p)] (A : ℕ)

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
