import Mathlib
import AKS.basic
-- import AKS.lemma_41

open Polynomial
variable (n p r : ℕ) (hrnz : r ≠ 0) [Fact (Nat.Prime p)] (A : ℕ)

-- TODO: maybe switch a ≡ b [MOD k] to k ∣ a-b (that's what we use in practice anyway).
lemma lemma42 (a b : ℕ)
  (ha : a ∈ S n p r)
  (hb : b ∈ S n p r)
  (hab : a ≡ b [MOD r]) :
  a ≡ b [MOD Nat.card (G n p r hrnz)] := by

  wlog hineq : a ≥ b
  . have fact : b ≥ a := Nat.le_of_not_ge hineq
    exact (this n p r hrnz b a hb ha hab.symm fact).symm

  -- part one: for all polys g ∈ ℤ/p[x][x], x^r-1 ∣ g(x^a) - g(x^b)
  have part1 : ∀ g : (ZMod p)[X][X], AdjoinRoot.mk (f p r) (g.eval (X^a)) = AdjoinRoot.mk (f p r) (g.eval (X^b)) := by
    intro g

    let ab : (ZMod p)[X] := X^(a-b)-1
    have f_dvd_ab : f p r ∣ ab := by
      have : r ∣ a-b := (Nat.modEq_iff_dvd' hineq).mp (Nat.ModEq.symm hab)
      obtain ⟨k, hk⟩ := this
      unfold ab
      rw [hk]
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
  have part2 : ∀ g ∈ H n p r, g^a = g^b := by
    intro g hg
    rw [ha, hb] <;> try assumption

    have : α p r ^ a = α p r ^ b := calc
      _ = AdjoinRoot.mk (f p r) (X^a) := by rfl
      _ = AdjoinRoot.mk (f p r) ((X : (ZMod p)[X][X]).eval (X^a)) := by rw [eval_X]
      _ = AdjoinRoot.mk (f p r) ((X : (ZMod p)[X][X]).eval (X^b)) := part1 X
      _ = AdjoinRoot.mk (f p r) (X^b) := by rw[eval_X (x := X^b)]
      _ = _ := by rfl

    simp only [this]

  have : ∀ g ∈ H n p r, (φ p r hrnz g)^a = (φ p r hrnz g)^b
    := λ g hg ↦ calc
    _ = φ p r hrnz (g^a) := by rw [map_pow]
    _ = φ p r hrnz (g^b) := by rw[part2]; exact hg
    _ = (φ p r hrnz g)^b := by rw [map_pow]

  -- part 3: applying this to elements of G
  have : ∀ g ∈ G n p r hrnz, g^a = g^b := λ g ⟨q, hq, hqg⟩ ↦ by
    have := this q hq
    have := calc
      (rfl.mp (↑ g : 𝔽 p r))^a = (φ p r hrnz q)^a := by rw[← hqg]; rfl
      _ = (φ p r hrnz q)^b := this
      _ = (rfl.mp (↑ g : 𝔽 p r))^b := by rw[← hqg]; rfl

    exact Units.eq_iff.mp this

  have : ∀ g ∈ G n p r hrnz, g^(a-b) = 1 := by
    intro g hg
    have : g^(a-b) * g^b = 1 * g^b := by
      rw [pow_sub_mul_pow (h := hineq), one_mul, this g hg]
    exact mul_right_cancel this

  -- part 4: concluding that #G divides a-b
  -- switching to g : ↥ G instead of g ∈ G because that's what isCyclic_iff_exists_orderOf_eq_natCard gives you
  -- maybe should do that everywhere for consistency's sake
  have order_divides_ab : ∀ (g : ↥ (G n p r hrnz)), orderOf g ∣ a-b := by --substituting names for variables, here for a-b?
    intro g
    rw[orderOf_dvd_iff_pow_eq_one]
    have := this (↑ g) (g.property)
    exact SetLike.coe_eq_coe.mp this

  have : ∃ (g : ↥(G n p r hrnz)), orderOf g = Nat.card (G n p r hrnz) := isCyclic_iff_exists_orderOf_eq_natCard.mp inferInstance

  obtain ⟨g, hg⟩ := this

  have : orderOf g ∣ a-b
    := order_divides_ab g

  rw [← hg]
  symm
  exact (Nat.modEq_iff_dvd' hineq).mpr this
