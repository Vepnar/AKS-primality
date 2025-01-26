import Mathlib
import LeanTutorial.basic

variable (n p r : ℕ) (hrnz : r ≠ 0) [pprime : Fact (Nat.Prime p)]
  (hp : p ∣ n) (hnnoprdivs : no_prime_divisors_below n r) (hnnotperfpow : ¬ is_perfect_power n) (hnodd : Odd n) (hn_gt_one : n > 1)
  (childs_binomial_theorem : ∀ a ∈ Finset.range (A n r + 1),
    (α p r + ↑ a)^n = α p r^n + ↑ a)
  (hordern : orderOf (↑ n : ZMod r) > ⌊(Real.logb 2 n) ^ 2 ⌋₊)
  (hnnotprime : ¬ n.Prime)

def ℓ (ij : ℕ × ℕ) : (ZMod r)ˣ
  := n' n r hrnz hnnoprdivs ^ ij.1 * p' n p r hrnz hp hnnoprdivs ^ ij.2

include hnnotperfpow hn_gt_one hnnotprime in
lemma n_not_power_of_p : ∀ k : ℕ, p^k ≠ n
 := λ k f ↦ hnnotperfpow $ by
    use p, k
    constructor
    . exact Nat.Prime.one_lt pprime.out
    constructor
    . by_contra hk
      rw [ge_iff_le, not_le] at hk
      have : k = 0 ∨ k = 1 := sorry -- ask Alain
      cases this with
      | inl kzero => simp[kzero] at f; rw[f] at hn_gt_one; exact Nat.lt_irrefl n $ gt_iff_lt.mp hn_gt_one
      | inr kone => simp[kone] at f; rw[← f] at hnnotprime; exact hnnotprime pprime.out
    . exact f

include hnnotperfpow hn_gt_one hnnotprime hp in
lemma n_over_p_not_power_of_p : ∀ k : ℕ, p^k ≠ n/p
 := by
  intro k f
  replace f := calc
    p^(k+1) = p^k * p := rfl
    _ = n/p * p := by rw[f]
    _ = n := Nat.div_mul_cancel hp
  exact n_not_power_of_p n p hnnotperfpow hn_gt_one hnnotprime (k+1) f

noncomputable def T : Finset (ℕ × ℕ)
  := let K := Finset.range $ Nat.floor (Real.sqrt $ Nat.card $ R n p r hrnz hp hnnoprdivs) + 1
    K ×ˢ K

omit [Fact (Nat.Prime p)] in
lemma cardT : Nat.card (R n p r hrnz hp hnnoprdivs) < Nat.card (T n p r hrnz hp hnnoprdivs)
  := by
  unfold T
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_product,
    Real.nat_floor_real_sqrt_eq_nat_sqrt, Finset.card_range, gt_iff_lt]
  exact Nat.sqrt_lt.mp $ lt_add_one _

-- #check Finset.exists_ne_map_eq_of_card_lt_of_maps_to
--   (s := T n p r hrnz hp hnnoprdivs)
--   (t := Set.toFinset (R n p r hrnz hp hnnoprdivs))
--   (cardT _ _ _ _ _ _)
--   (f := ℓ n p r hrnz hp hnnoprdivs)


lemma upper_bound_G : Nat.card (G n p r hrnz) ≤ (n : ℝ)^(Real.sqrt (Nat.card (R n p r hrnz hp hnnoprdivs))) - 1
  := sorry
  -- by
  -- obtain := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
