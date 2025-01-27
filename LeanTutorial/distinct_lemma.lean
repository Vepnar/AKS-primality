import Mathlib
import LeanTutorial.basic

variable
  (n p : ℕ) [pprime : Fact (p.Prime)]
  (hn_not_power_of_p : ∀ k, p^k ≠ n) (hn_gt_one : n > 1)

def m (ij : ℕ × ℕ) : ℕ
  := n ^ ij.1 * p ^ ij.2

omit pprime in
lemma ub_m (hn : n ≥ 1) (hp : p ≥ 1) (C : ℕ) (ij : ℕ × ℕ) (h₁ : ij.1 ≤ C) (h₂ : ij.2 ≤ C)
  : m n p ij ≤ n^C * p^C := by
  unfold m
  apply Nat.mul_le_mul
  repeat
    (apply Nat.pow_le_pow_of_le_right; assumption; assumption)

omit pprime in
lemma lb_m (hn : n ≥ 1) (hp : p ≥ 1) (ij : ℕ × ℕ)
  : 1 ≤ m n p ij := by
  unfold m
  apply one_le_mul
  repeat (apply one_le_pow₀; assumption)

include hn_not_power_of_p hn_gt_one in
lemma distinct : Function.Injective (m n p)
  := by
  intro ⟨ i₁, j₁ ⟩ ⟨ i₂, j₂ ⟩ eq
  wlog iineq : i₁ ≥ i₂
  . have fact : i₁ ≤ i₂ := by refine Nat.le_of_not_ge iineq
    symm
    exact this n p hn_not_power_of_p hn_gt_one i₂ j₂ i₁ j₁ eq.symm fact

  have nnezero : n ≠ 0 := ne_of_gt (by linarith)
  have pnezero : p ≠ 0 := Nat.Prime.ne_zero pprime.out

  unfold m at eq
  simp only [Prod.mk.injEq]
  simp only at eq

  have lemi : i₂ + (i₁ - i₂) = i₁ := by simp only [add_tsub_cancel_of_le, iineq]
  have p1 : n ^ i₁ = n^i₂ * n ^ (i₁-i₂) := by rw [← Nat.pow_add, lemi];
  rw [p1, mul_assoc] at eq
  replace eq := mul_left_cancel₀ (pow_ne_zero i₂ nnezero) eq

  have jineq : j₂ ≥ j₁ := by
    by_contra ifnot
    replace ifnot : j₂ < j₁ := Nat.gt_of_not_le ifnot
    have part1 : p^j₂ < p^j₁ := Nat.pow_lt_pow_of_lt (Nat.Prime.one_lt pprime.out) ifnot
    have part2 : n^(i₁ - i₂) ≥ 1 := one_le_pow₀ (Nat.zero_lt_of_ne_zero nnezero)
    have : 1 * p^j₂ < n^(i₁ - i₂) * p^j₁ := mul_lt_mul_of_pos_of_nonneg part2 part1 (by norm_num) (Nat.zero_le (p ^ j₁))
    rw [one_mul, ← eq] at this
    exact lt_irrefl (n ^ (i₁ - i₂) * p ^ j₁) this

  have lemj : (j₂ - j₁) + j₁ = j₂ := by simp only [jineq, tsub_add_cancel_of_le]
  have p2 : p^j₂ = p^(j₂ - j₁) * p^j₁ := by rw [← Nat.pow_add, lemj]
  rw [p2] at eq
  replace eq := mul_right_cancel₀ (pow_ne_zero j₁ pnezero) eq

  let i := i₁ - i₂
  let j := j₂ - j₁
  suffices : i = 0 ∧ j = 0
  . unfold i j at this
    rw [← Nat.add_right_cancel_iff (n := i₂), ← Nat.add_right_cancel_iff (m := j₂-j₁) (n := j₁),
        Nat.sub_add_cancel iineq, Nat.sub_add_cancel jineq,
        Nat.zero_add, Nat.zero_add] at this
    tauto

  replace eq := calc
    n ^ i = n^(i₁ - i₂) := rfl
    _     = p^(j₂ - j₁) := eq
    _     = p ^ j := rfl

  suffices : i = 0
  . simp only [this, true_and]
    simp only [this, pow_zero] at eq
    replace eq := eq.symm
    by_contra j_nzero
    rw [pow_eq_one_iff j_nzero] at eq
    exact Nat.Prime.ne_one (pprime.out) eq

  by_contra i_nzero
  have := (calc
    i * multiplicity p n = multiplicity p (n^i) := Eq.symm $
      FiniteMultiplicity.multiplicity_pow
        (Nat.Prime.prime pprime.out)
        (Nat.finiteMultiplicity_iff.mpr
          (And.intro (Nat.Prime.ne_one pprime.out) (by linarith)))
    _ = multiplicity p (p^j) := by rw[eq]
    _ = j := multiplicity_pow_self_of_prime (Nat.Prime.prime pprime.out) j)

  rw[← this, mul_comm, pow_mul, pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) i_nzero] at eq
  exfalso
  exact hn_not_power_of_p (multiplicity p n) eq.symm
