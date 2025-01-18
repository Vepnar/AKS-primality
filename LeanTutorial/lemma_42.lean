import Mathlib
import LeanTutorial.basic
-- import LeanTutorial.lemma_41

open Polynomial
variable (p r : ℕ) (hrnz : r ≠ 0) [Fact (Nat.Prime p)] (A : ℕ)

-- TODO: maybe switch a ≡ b [MOD k] to k ∣ a-b (that's what we use in practice anyway).
lemma lemma42 (a b : ℕ)
  (hineq : a ≥ b)
  (ha : a ∈ S p r A)
  (hb : b ∈ S p r A)
  (hab : a ≡ b [MOD r]) :
  a ≡ b [MOD Nat.card (G p r hrnz A)] := by

  -- part one: for all polys g ∈ ℤ/p[x][x], x^r-1 ∣ g(x^a) - g(x^b)
  have part1 : ∀ g : (ZMod p)[X][X], AdjoinRoot.mk (f p r) (g.eval (X^a)) = AdjoinRoot.mk (f p r) (g.eval (X^b)) := by
    intro g

    let ab : (ZMod p)[X] := X^(a-b)-1
    have f_dvd_ab : f p r ∣ ab := by
      let k := (a - b)/r
      have : r ∣ a-b := (Nat.modEq_iff_dvd' hineq).mp (Nat.ModEq.symm hab)
      have : r * k = a-b := Nat.mul_div_cancel' this
      unfold ab
      rw [←this]
      have := sub_dvd_pow_sub_pow (X^r : (ZMod p)[X]) 1 k
      rw [one_pow, ← pow_mul] at this
      exact this

    let xaxb : (ZMod p)[X] := X^a - X^b
    have ab_dvd_xaxb : ab ∣ xaxb := by
      constructor
      rotate_left 1
      . exact X^b
      . ring_nf
        rw [← pow_add, add_comm b (a-b), Nat.sub_add_cancel hineq]
        ring

    have xaxb_dvd_gxagxb : xaxb ∣ g.eval (X^a) - g.eval (X^b)
      := sub_dvd_eval_sub (X^a) (X^b) g

    have : f p r ∣ g.eval (X^a) - g.eval (X^b)
      := dvd_trans (dvd_trans f_dvd_ab ab_dvd_xaxb) xaxb_dvd_gxagxb

    exact eq_of_sub_eq_zero (AdjoinRoot.mk_eq_zero.mpr this)

  -- part 2: applying this to elements of H
  have part2 : ∀ g ∈ H p r A, g^a = g^b := by
    intro g hg
    rw [ha, hb] <;> try assumption

    have : α p r ^ a = α p r ^ b := calc
      _ = AdjoinRoot.mk (f p r) (X^a) := by rfl
      _ = AdjoinRoot.mk (f p r) ((X : (ZMod p)[X][X]).eval (X^a)) := by rw [eval_X]
      _ = AdjoinRoot.mk (f p r) ((X : (ZMod p)[X][X]).eval (X^b)) := part1 X
      _ = AdjoinRoot.mk (f p r) (X^b) := by rw[eval_X (x := X^b)]
      _ = _ := by rfl

    simp only [this]

  have : ∀ g ∈ H p r A, (AdjoinRoot.algHomOfDvd (h_div p r hrnz) g)^a = (AdjoinRoot.algHomOfDvd (h_div p r hrnz) g)^b
    := λ g hg ↦ calc
    _ = AdjoinRoot.algHomOfDvd (h_div p r hrnz) (g^a) := by simp only [map_pow]
    _ = AdjoinRoot.algHomOfDvd (h_div p r hrnz) (g^b) := by rw[part2]; assumption
    _ = (AdjoinRoot.algHomOfDvd (h_div p r hrnz) g)^b := by simp only [map_pow]

  -- part 3: applying this to elements of G
  have : ∀ g ∈ G p r hrnz A, g^a = g^b := λ g ⟨q, hq, hqg⟩ ↦ by
    have := this q hq
    have := (calc
    (rfl.mp (↑ g : 𝔽 p r))^a = (AdjoinRoot.algHomOfDvd (h_div p r hrnz) q)^a := by rw[← hqg]; rfl
    _ = (AdjoinRoot.algHomOfDvd (h_div p r hrnz) q)^b := this
    _ = (rfl.mp (↑ g : 𝔽 p r))^b := by rw[← hqg]; rfl)

    exact Units.eq_iff.mp this

  have : ∀ g ∈ G p r hrnz A, g^(a-b) = 1 := by
    intro g hg
    have : g^(a-b) * g^b = 1 * g^b := by
      rw [pow_sub_mul_pow (h := hineq), one_mul, this g hg]
    exact mul_right_cancel this

  -- part 4: concluding that #G divides a-b
  -- switching to g : ↥ G instead of g ∈ G because that's what isCyclic_iff_exists_orderOf_eq_natCard gives you
  -- maybe should do that everywhere for consistency's sake
  have order_divides_ab : ∀ (g : ↥ (G p r hrnz A)), orderOf g ∣ a-b := by --substituting names for variables, here for a-b?
    intro g
    rw[orderOf_dvd_iff_pow_eq_one]
    have := this (↑ g) (g.property)
    apply SetLike.coe_eq_coe.mp
    exact this

  have : ∃ (g : ↥(G p r hrnz A)), orderOf g = Nat.card (G p r hrnz A) := isCyclic_iff_exists_orderOf_eq_natCard.mp inferInstance

  let g := Classical.choose this
  have hg : orderOf g = Nat.card (G p r hrnz A) := Classical.choose_spec this

  have : orderOf g ∣ a-b
    := order_divides_ab g

  rw [← hg]
  apply Nat.ModEq.symm
  exact (Nat.modEq_iff_dvd' hineq).mpr this
