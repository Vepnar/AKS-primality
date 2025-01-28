import Mathlib
import LeanTutorial.basic
open Polynomial

variable (n p r : ℕ) (hrnz : r ≠ 0) [pprime : Fact (Nat.Prime p)]
  (hnnoprdivs : no_prime_divisors_below n r)
  (hnnotperfpow : ¬ is_perfect_power n)  [hge1: Fact (n ≥ 1)] -- use a weaker assumption, have a bit more general lemma

lemma logb_base2_ge_one {n : ℕ} (hn : n ≥ 2) : 1 ≤ Real.logb 2 n := by
    cases n
    exfalso
    exact Nat.not_succ_le_zero 1 hn
    case succ n =>
    rw[Real.le_logb_iff_rpow_le]
    simp
    rw[ge_iff_le] at hn
    rify at hn
    exact hn
    exact one_lt_two
    have : 0 < n + 1 := by
      exact Nat.zero_lt_succ n
    rify at this
    simp
    exact this

lemma nge2 (hn' : p ∣ n) : n ≥ 2 := by
    have pprime := pprime.out
    have nge0 := hge1.out
    have zero_lt_n : 0 < n := lt_of_lt_of_le (zero_lt_one) nge0
    have p_le_n : p ≤ n := Nat.le_of_dvd zero_lt_n hn'
    have pge2 : 2 ≤ p := Nat.Prime.two_le pprime
    apply lt_of_lt_of_le pge2 p_le_n

lemma lemma43' (g q : Polynomial (ZMod p))
  (hg : AdjoinRoot.mk (h p r) g ∈ Gmonoid n p r hrnz) (hq : AdjoinRoot.mk (h p r) q ∈ Gmonoid n p r hrnz)
  (hmod : AdjoinRoot.mk (h p r) g = AdjoinRoot.mk (h p r) q)
  (hdegg : Polynomial.natDegree g < Nat.card (R n p r hrnz hp hnnoprdivs)) (hdegq : Polynomial.natDegree q < Nat.card (R n p r hrnz hp hnnoprdivs))
  : g = q := by
  let Δ := g - q
  let Δ' := AdjoinRoot.mk (h p r) Δ

  -- have lem_g : AdjoinRoot.mk (f p r) g ∈ H n p r := sorry

  obtain ⟨g', hg'₁, hg'₂⟩ := hg
  obtain ⟨q', hq'₁, hq'₂⟩ := hq

  have : ∀ k ∈ S n p r, Δ.aeval (β p r^k) = 0
    := by
    intro k hk
    unfold Δ
    simp
    suffices : g.aeval (α p r^k) = q.aeval (α p r^k)
    . have := congrArg (φ p r hrnz) this
      rw [← aeval_algHom_apply (φ p r hrnz), ← aeval_algHom_apply (φ p r hrnz)] at this
      simp[φ, α, AdjoinRoot.algHomOfDvd_apply_root] at this
      exact sub_eq_zero_of_eq this
    have := (restatement_S₂ n p r k).mp hk g sorry
    rw[this, (restatement_S₂ n p r k).mp hk q sorry]
    congr 1
    -- hmmmmm. on the right track though.
    sorry

  have : Δ.natDegree < Nat.card (R n p r hrnz hp hnnoprdivs) := by
    have : 1 ≤ Nat.card (R n p r hrnz hp hnnoprdivs) := by sorry
    rw [Nat.lt_iff_le_pred this] at hdegg hdegq ⊢
    unfold Δ
    exact (Polynomial.natDegree_sub_le_iff_left hdegq).mpr hdegg

  have : ∀ k ∈ R n p r hrnz hp hnnoprdivs, ∃ k' ∈ S n p r, k' = k.val
    := sorry
  let fn (k : R n p r hrnz hp hnnoprdivs) : S n p r := sorry
  have : ∀ (k : R n p r hrnz hp hnnoprdivs), k.val.val = fn k := sorry
  have : Function.Injective fn := sorry

  -- use Polynomial.card_roots'

  sorry

  -- have helper' (k : ℕ) : (h p r).aeval (β p r^k) = 0 := sorry

  -- have : ∀ k ∈ S n p r, Δ'.liftHom (h p r) (β p r^k) (helper' k) = 0
  --   := by
  --   intro k hk
  --   obtain ⟨g', hg'₁, hg'₂⟩ := hg
  --   obtain ⟨q', hq'₁, hq'₂⟩ := hq
  --   calc
  --   Δ'.liftHom (h p r) (β p r^k) (helper' k)
  --     = (AdjoinRoot.mk (h p r) g).liftHom (h p r) (β p r^k) (helper' k) - (AdjoinRoot.mk (h p r) q).liftHom (h p r) (β p r^k) (helper' k) := by simp[Δ, Δ']
  --   _ = (AdjoinRoot.algHomOfDvd (h_div p r hrnz) g').liftHom (h p r) (β p r^k) (helper' k) - (AdjoinRoot.algHomOfDvd (h_div p r hrnz) q').liftHom (h p r) (β p r^k) (helper' k) := by rw[← hg'₂,← hq'₂]; rfl
  --   _ = (AdjoinRoot.algHomOfDvd (h_div p r hrnz) g').liftHom (h p r) (β p r^k) (helper' k) - (AdjoinRoot.algHomOfDvd (h_div p r hrnz) q').liftHom (h p r) (β p r^k) (helper' k) := by rfl
  --   _ = 0 := sorry

  -- sorry

lemma lemma43 (g q : Polynomial (ZMod p))
  (hg : AdjoinRoot.mk (h p r) g ∈ Gmonoid n p r hrnz) (hq : AdjoinRoot.mk (h p r) q ∈ Gmonoid n p r hrnz)
  (hmod : AdjoinRoot.mk (h p r) g = AdjoinRoot.mk (h p r) q)
  (hdegg : Polynomial.degree g < Nat.card (R n p r hrnz hp hnnoprdivs)) (hdegq : Polynomial.degree q < Nat.card (R n p r hrnz hp hnnoprdivs))
  : g = q := by
  let Δ := g - q
  have hΔmod : ∀ k ∈ S n p r, AdjoinRoot.mk (h p r) (Δ.comp X^k) = 0
  intro w -- changed X to w so it is not confused with X variable, you can always change it back
  simp
  intro hX

  constructor
  . rw[AdjoinRoot.mk_eq_mk] at hmod
    exact hmod
  show w ≠ 0
  by_contra hw
  rw[hw] at hX
  unfold S at hX
  simp at hX
  specialize hX (AdjoinRoot.mk (f p r) (X + 1))
  simp at hX
  have polinH: AdjoinRoot.root (f p r) + 1 ∈ H n p r := by
    unfold H
    apply Submonoid.subset_closure
    unfold α
    use 1
    simp
    unfold A
    apply Nat.le_floor
    simp
    refine one_le_mul_of_one_le_of_one_le ?_ ?_
    swap
    rw[Real.one_le_sqrt]
    -- linarith
    simp
    exact Nat.zero_lt_of_ne_zero (by trivial)
    apply logb_base2_ge_one (nge2 n p hp)
  have eqq := by exact (hX polinH)
  have eqq': (AdjoinRoot.mk (f p r)) 1  = (AdjoinRoot.mk (f p r)) 0 := by
    simp
    exact eqq

  have p_ndiv_one : ¬ p ∣ 1 := Nat.Prime.not_dvd_one pprime.out
  have : NeZero (1 : AdjoinRoot (f p r)) := by
    haveI : CharP (AdjoinRoot (f p r)) p := instCharPAdjoinRootF _ _ hrnz
    have := NeZero.of_not_dvd (AdjoinRoot (f p r)) p_ndiv_one
    simp at *
    assumption

  have contrad := this.out eqq'
  exact contrad

  -- rw[AdjoinRoot.mk_eq_mk] at eqq'
  -- simp at eqq'
  -- rw[dvd_iff_exists_eq_mul_left] at eqq'
  -- cases' eqq' with o1 o2
  -- apply_fun Polynomial.natDegree at o2
  -- rw[Polynomial.natDegree_mul] at o2
  -- simp at o2
  -- have degf : (f p r).natDegree = r := by sorry
  -- --rw[degf] at o2
  -- rw[eq_comm] at o2
  -- rw[Nat.add_eq_zero_iff] at o2
  -- cases' o2 with o2 o3
  -- rw[o3] at degf
  -- rw[eq_comm] at degf
  -- exact (hrnz degf)

  -- by_contra t
  -- rw[t] at o2
  -- simp at o2

  rw[AdjoinRoot.mk_eq_mk, dvd_iff_exists_eq_mul_left] at hmod
  cases' hmod with u uu
  rw[sub_eq_iff_eq_add] at uu
  rw[uu, add_left_eq_self]
  rw[← add_neg_eq_iff_eq_add] at uu
  simp

  have orderX : orderOf (β p r) = r := order_of_X_in_F p r hrnz

  sorry
