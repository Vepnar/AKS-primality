import Mathlib
import LeanTutorial.basic

variable (n p r : ℕ) (hrnz : r ≠ 0) [Fact (Nat.Prime p)]
  (hp : p ∣ n) (hnnoprdivs : no_prime_divisors_below n r) (hnnotperfpow : ¬ is_perfect_power n) (hnodd : Odd n) (hnge1 : n > 1)
  (childs_binomial_theorem : ∀ a ∈ Finset.range (A n r + 1),
    (α p r + ↑ a)^n = α p r^n + ↑ a)
  (hordern : orderOf (↑ n : ZMod r) > ⌊(Real.logb 2 n) ^ 2 ⌋₊)

def ℓ (ij : ℕ × ℕ) : (ZMod r)ˣ
  := n' n r hrnz hnnoprdivs ^ ij.1 * p' n p r hrnz hp hnnoprdivs ^ ij.2

def m (ij : ℕ × ℕ) : ℕ
  := n ^ ij.1 * p ^ ij.2

include hnodd hnnotperfpow in
lemma distinct : Function.Injective (m n p)
  := by
  intro ⟨ i₁, j₁ ⟩ ⟨ i₂, j₂ ⟩ eq
  wlog iineq : i₁ ≥ i₂
  . have fact : i₁ ≤ i₂ := by refine Nat.le_of_not_ge (by assumption)
    symm
    exact this n p hnnotperfpow hnodd i₂ j₂ i₁ j₁ eq.symm fact

  unfold m at eq
  simp only [Prod.mk.injEq]
  simp only at eq

  have lemi : i₂ + (i₁ - i₂) = i₁ := by simp only [add_tsub_cancel_of_le, iineq]

  have p1 : n ^ i₁ = n^i₂ * n ^ (i₁-i₂) := by rw [← Nat.pow_add, lemi];

  -- n is nonzero since it is odd
  have nnezero : n ≠ 0 := λ nzero ↦ by
    rw [nzero] at hnodd
    exact Nat.not_odd_zero hnodd

  have pnezero : p ≠ 0 := Nat.Prime.ne_zero (inferInstanceAs (Fact p.Prime)).out

  rw [p1, mul_assoc] at eq
  replace eq := mul_left_cancel₀ (pow_ne_zero i₂ nnezero) eq

  have jineq : j₂ ≥ j₁ := by
    by_contra ifnot
    replace ifnot : j₂ < j₁ := Nat.gt_of_not_le ifnot
    have part1 : p^j₂ < p^j₁ := Nat.pow_lt_pow_of_lt (Nat.Prime.one_lt (inferInstanceAs (Fact p.Prime)).out) ifnot
    have part2 : n^(i₁ - i₂) ≥ 1 := one_le_pow₀ (Nat.zero_lt_of_ne_zero nnezero)
    have : 1 * p^j₂ < n^(i₁ - i₂) * p^j₁ := mul_lt_mul_of_pos_of_nonneg part2 part1 (by norm_num) (Nat.zero_le (p ^ j₁))
    rw [one_mul, ← eq] at this
    exact (lt_self_iff_false (n ^ (i₁ - i₂) * p ^ j₁)).mp this

  have lemj : (j₂ - j₁) + j₁ = j₂ := by simp only [jineq, tsub_add_cancel_of_le]
  have p2 : p^j₂ = p^(j₂ - j₁) * p^j₁ := by rw [← Nat.pow_add, lemj]
  rw [p2] at eq
  replace eq := mul_right_cancel₀ (pow_ne_zero j₁ pnezero) eq

  let i := i₁ - i₂
  let j := j₂ - j₁
  suffices : i = 0 ∧ j = 0
  . simp only [i, j] at this
    rw [← Nat.add_right_cancel_iff (n := i₂), ← Nat.add_right_cancel_iff (m := j₂-j₁) (n := j₁),
        Nat.sub_add_cancel iineq, Nat.sub_add_cancel jineq,
        Nat.zero_add, Nat.zero_add] at this
    tauto
  replace eq := calc
    n ^ i = n^(i₁ - i₂) := rfl
    _     = p^(j₂-j₁) := eq
    _     = p ^ j := rfl

  let k := multiplicity p n
  have : p^k ∣ n := pow_multiplicity_dvd p n
  have : p^k ≠ n := λ f ↦ hnnotperfpow $ by
    use p, k
    constructor
    . exact Nat.Prime.one_lt (inferInstanceAs (Fact p.Prime)).out
    constructor
    . sorry
    . exact f

  sorry

noncomputable def T : Finset (ℕ × ℕ)
  := let K := (Finset.range (Nat.sqrt (Nat.card (R n p r hrnz hp hnnoprdivs))));
    Finset.product K K

-- lemma cardT : (R n p r hrnz hp hnnoprdivs).carrier.toFinset.card < (T p r n).card
--   := by
--   -- case on whether R is a square
--   sorry

-- #check λ (n : ℕ) ↦ Finset.exists_ne_map_eq_of_card_lt_of_maps_to
--   (s := T p r n)
--   (t := Set.toFinset (R p r n).carrier)
--   (cardT _ _ _)
--   (f := ℓ p n)
