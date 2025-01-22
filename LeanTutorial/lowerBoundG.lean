import Mathlib
import LeanTutorial.basic

variable (n p r : ℕ) (hrnz : r ≠ 0) [Fact (Nat.Prime p)]
  (hp : p ∣ n) (hnnoprdivs : no_prime_divisors_below n r) (hnnotperfpow : ¬ is_perfect_power n) (hnodd : Odd n) (hn_gt_one : n > 1)
  (childs_binomial_theorem : ∀ a ∈ Finset.range (A n r + 1),
    (α p r + ↑ a)^n = α p r^n + ↑ a)
  (hordern : orderOf (↑ n : ZMod r) > ⌊(Real.logb 2 n) ^ 2 ⌋₊)

omit [Fact (Nat.Prime p)] in
lemma ord_R : Nat.card (R n p r hrnz hp hnnoprdivs) ≥ d n r := by
  -- for in the report: this is definition no. 3
  -- first I tried making it a subgroup of R
  -- then I defined it as Subgroup.closure {n' n r hrnz hnnoprdivs}.
  -- this is definitely best
  let sub : Subgroup (ZMod r)ˣ := Subgroup.zpowers (n' n r hrnz hnnoprdivs)
  have sub_in_R : sub ≤ R n p r hrnz hp hnnoprdivs := by
    apply Subgroup.zpowers_le_of_mem
    apply Subgroup.subset_closure
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]

  suffices : Nat.card sub = d n r
  . rw[← this]
    exact Subgroup.card_le_of_le sub_in_R

  have ninsub : n' n r hrnz hnnoprdivs ∈ sub := by
    simp only [Subgroup.mem_zpowers, sub]

  rw [Nat.card_zpowers]
  simp only [Subgroup.orderOf_mk, n', ← orderOf_units, ZMod.coe_unitOfCoprime]
  rfl

noncomputable def B : ℕ :=
  ⌊ Real.logb 2 n * Real.sqrt (Nat.card (R n p r hrnz hp hnnoprdivs)) ⌋₊

lemma AgtB : A n r > B n p r hrnz hp hnnoprdivs := by
  unfold A B
  sorry

include hordern in
lemma cardRgtB : Nat.card (R n p r hrnz hp hnnoprdivs) > B n p r hrnz hp hnnoprdivs
  := by
  apply lt_of_lt_of_le _ (ord_R n p r hrnz hp hnnoprdivs)
  trans ⌊ (Real.logb 2 n)^2 ⌋₊
  rify
  rotate_left
  . unfold d
    exact hordern
  . sorry

-- todo: maybe leave hT out.
open Polynomial in
noncomputable def prod_factors (T : Finset (Finset.range (B n p r hrnz hp hnnoprdivs + 1)))
  (hT : T ≠ univ) : G n p r hrnz
  := ∏ a ∈ T, sorry

lemma lower_bound_G : Nat.card (G n p r hrnz) > (n : ℝ)^(Real.sqrt (Nat.card (R n p r hrnz hp hnnoprdivs))) - 1
  := sorry
