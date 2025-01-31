import Mathlib
import AKS.basic
import AKS.lemma_41
open Polynomial

variable (n p r : ℕ) (hrnz : r ≠ 0) [pprime : Fact (Nat.Prime p)]
  (hp : p ∣ n) (hnnoprdivs : no_prime_divisors_below n r) (hnnotperfpow : ¬ is_perfect_power n) (hnodd : Odd n) (hn_gt_one : n > 1)
  (childs_binomial_theorem : ∀ a ∈ Finset.range (A n r + 1),
    (α p r + ↑ a)^n = α p r^n + ↑ a)
  (hordern : orderOf (↑ n : ZMod r) > ⌊(Real.logb 2 n) ^ 2 ⌋₊)

lemma card_rootSet_le_card_aroots {R A : Type*} [Field R] [CommRing A] [IsDomain A] [Algebra R A]
  (g : R[X]) : Nat.card (g.rootSet A) ≤ (g.aroots A).card
  := by
  classical
  simp only [Nat.card_eq_fintype_card, rootSet]
  simp_all only [Finset.coe_sort_coe, Multiset.mem_toFinset, mem_roots', ne_eq, Polynomial.map_eq_zero, IsRoot.def,
    eval_map_algebraMap, Fintype.card_coe]
  exact Multiset.toFinset_card_le (g.aroots A)

set_option maxHeartbeats 1000000

include childs_binomial_theorem hn_gt_one hordern in
lemma lemma43 (g q : Polynomial (ZMod p))
  (hg' : AdjoinRoot.mk (f p r) g ∈ H n p r) (hq' : AdjoinRoot.mk (f p r) q ∈ H n p r)
  (hmod : AdjoinRoot.mk (h p r) g = AdjoinRoot.mk (h p r) q)
  (hdegg' : Polynomial.degree g < Nat.card (R n p r hrnz hp hnnoprdivs)) (hdegq' : Polynomial.degree q < Nat.card (R n p r hrnz hp hnnoprdivs))
  : g = q := by

  let Δ := g - q

  suffices : Δ = 0
  . exact sub_eq_zero.mp this
  -- the idea of this proof is to show that Δ has too many roots for it not to be the zero polynomial.
  -- Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
  -- doesn't quite work for us, as the roots of Δ lie in an algebra over ZMod p.
  -- instead, we do it a bit more manually.

  by_contra Δ_nzero

  have is_root : ∀ k ∈ S n p r, Δ.aeval (β p r^k) = 0
    := by
    intro k hk
    unfold Δ
    simp
    suffices : g.aeval (β p r^k) = q.aeval (β p r^k)
    . exact sub_eq_zero_of_eq this
    have eqg := consequence_S n p r hrnz k hk g hg'
    have eqq := consequence_S n p r hrnz k hk q hq'
    rw[eqg, eqq]
    congr

  have hdegΔ : Δ.degree < Nat.card (R n p r hrnz hp hnnoprdivs) := by
    cases Classical.em (g = 0) with
    | inl hg => simpa [Δ, hg]
    | inr hg => cases Classical.em (q = 0) with
      | inl hq => simpa [Δ, hq]
      | inr hq =>

    rw [← Polynomial.natDegree_lt_iff_degree_lt] at hdegg' hdegq' ⊢ <;> try assumption
    have : 1 ≤ Nat.card (R n p r hrnz hp hnnoprdivs) := by
      haveI : Fintype (R n p r hrnz hp hnnoprdivs) := instRFintype n p r hrnz hp hnnoprdivs
      rw[Nat.card_eq_fintype_card]
      exact Fintype.card_pos
    rw [Nat.lt_iff_le_pred this] at hdegg' hdegq' ⊢
    exact (Polynomial.natDegree_sub_le_iff_left hdegq').mpr hdegg'

  have : ∀ k ∈ R n p r hrnz hp hnnoprdivs, ∃ (k' : S n p r), k' = k.val
    := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      cases hx with
      | inl hx =>
        use ⟨n, ninS n p r childs_binomial_theorem⟩
        simp[hx, n']
      | inr hx =>
        use ⟨p, pinS n p r⟩
        simp[hx, p']
    | one =>
      use ⟨1, one_in_S n p r⟩
      simp
    | mul x y hx hy hx₂ hy₂ =>
      obtain ⟨⟨k₁', k₁'_in_S⟩, hk₁'⟩ := hx₂
      obtain ⟨⟨k₂', k₂'_in_S⟩, hk₂'⟩ := hy₂
      use ⟨k₁' * k₂', lemma41 n p r _ _ k₁'_in_S k₂'_in_S⟩
      simp[hk₁', hk₂']
    | inv x hx ih =>
      -- TODO: is there no induction principle to eliminate this step in case of a finite group?
      -- or something like: a finite submonoid is a subgroup?
      -- can't find anything
      let o := orderOf x
      have : x⁻¹ = x^(o-1) := by
        refine Eq.symm (eq_inv_of_mul_eq_one_left ?_)
        nth_rw 2 [← pow_one x]
        rw [← pow_add, Nat.sub_add_cancel (orderOf_pos x)]
        exact pow_orderOf_eq_one x
      rw[this]
      obtain ⟨⟨i, hi₁⟩, hi₂⟩ := ih
      use ⟨i^(o-1), pow_in_S n p r _ _ hi₁⟩
      simp[hi₂]

  let fn (k : R n p r hrnz hp hnnoprdivs) : S n p r :=
    Classical.choose $ this k k.property

  have fn_prop (k : R n p r hrnz hp hnnoprdivs) : fn k = k.val.val:=
    Classical.choose_spec (this k k.property)

  let fn' (k : R n p r hrnz hp hnnoprdivs) := by
    let e := fn k
    exact β p r^e.val

  have fn'_root (k : R n p r hrnz hp hnnoprdivs) : fn' k ∈ Δ.rootSet _ := by
    rw[Polynomial.mem_rootSet]
    simp only [ne_eq, Δ_nzero, not_false_eq_true, true_and]
    unfold fn'
    exact is_root (fn k) (fn k).property

  let fn'' (k : R n p r hrnz hp hnnoprdivs) : Δ.rootSet _ :=
    ⟨ fn' k, fn'_root k ⟩

  have fn''_inj : Function.Injective fn'' := by
    have β_nzero : β p r ≠ 0 := by
      have := nz_of_β_add_x n p r hrnz hp hnnoprdivs hn_gt_one childs_binomial_theorem hordern 0 (Finset.mem_range.mpr (Nat.zero_lt_succ (A n r)))
      simp at this
      exact this

    let γ := Units.mk0 (β p r) β_nzero
    have γ_order : orderOf γ = orderOf (β p r) := orderOf_eq_orderOf_iff.mpr $ by
      intro n
      simp[γ, ← Units.eq_iff]

    intro x y hxy
    unfold fn'' fn' at hxy
    rw[Subtype.mk_eq_mk] at hxy
    simp only at hxy

    replace hxy : γ ^ ((fn x).val) = γ ^ ((fn y).val)
      := by
      rw[← Units.eq_iff]
      simp[γ,hxy]

    rw[← mul_one (γ ^ _)] at hxy
    replace hxy := div_eq_of_eq_mul' hxy.symm
    rw[← zpow_natCast_sub_natCast] at hxy
    replace hxy := orderOf_dvd_iff_zpow_eq_one.mpr hxy
    rw[γ_order, order_of_X_in_F _ _ _ hrnz hp hnnoprdivs,
      ← ZMod.intCast_eq_intCast_iff_dvd_sub, Int.cast_natCast, Int.cast_natCast,
      fn_prop x, fn_prop y] at hxy

    apply Subtype.eq
    apply Units.eq_iff.mp
    exact hxy

  have : Nat.card (R n p r hrnz hp hnnoprdivs) ≤ Nat.card (Δ.rootSet (𝔽 p r)) :=
    Nat.card_le_card_of_injective fn'' fn''_inj

  have := calc
    Nat.card ↥(R n p r hrnz hp hnnoprdivs) ≤ Nat.card ↑(Δ.rootSet (𝔽 p r)) := this
    _ ≤ (Δ.aroots (𝔽 p r)).card := card_rootSet_le_card_aroots Δ
    _ = (Δ.map (algebraMap _ _)).roots.card := by rw[aroots_def]
    _ ≤ (Δ.map (algebraMap _ _)).natDegree := Polynomial.card_roots' $ Δ.map (algebraMap _ _)
    _ = Δ.natDegree := Polynomial.natDegree_map (algebraMap (ZMod p) (𝔽 p r))
    _ < Nat.card (R n p r hrnz hp hnnoprdivs) := (Polynomial.natDegree_lt_iff_degree_lt Δ_nzero).mpr hdegΔ

  exact Nat.lt_irrefl _ this
