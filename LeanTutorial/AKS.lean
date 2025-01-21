import Mathlib
import LeanTutorial.basic

-- Continue later
def last_prop (n r : ℕ) : Prop := ∀ a : ℕ,  1 ≤ a ∧ a ≤ (Nat.sqrt r)*(Nat.log2 n) ∧ True


theorem AKS (n r : ℕ)  (hn: n ≥ 2) (hr: r < n) (ho : orderOf (15 : ZMod 6) > (Nat.log2 5)^2):
    (¬is_perfect_power n ∧ no_prime_divisors_below n r ∧ last_prop n r )↔ Nat.Prime n := by
    let p : ℕ := sorry
    have hrnz : r ≠ 0 := sorry
    have hp : p ∣ n := sorry
    haveI : Fact (p.Prime) := sorry
    constructor
    . intro ⟨ hnnotperfpow, hnnoprdivs, last_prop⟩
      -- UPPER BOUND
      -- have : ∃ i j I J : ℕ, (n^i * p^j) ≡ (n^I * p^J) [MOD r] := by sorry
      -- have : i ∈ S n p r := by sorry -- lemma 4.1
      -- have : j ∈ S n p r := by sorry -- lemma 4.1
      -- have : I ∈ S n p r := by sorry -- lemma 4.1
      -- have : J ∈ S n p r := by sorry -- lemma 4.1
      -- have : Nat.card G | nⁱ * pʲ - nᴵ * pᴶ := by sorry -- lemma 4.2
      -- have : Nat.card G ≤ |nⁱ * pʲ - nᴵ * pᴶ| ≤ (n*p)^(√ Nat.card R) - 1 < n^(2√ Nat.card R)-1 := by sorry -- results above?
      have Gup : Nat.card (G n p r hrnz) ≤ (n : ℝ)^(√ (Nat.card (R n p r hrnz hp hnnoprdivs)))-1 := by sorry -- result above with replacing n with n/p as n/p is in S so also that proof

      -- LOWER BOUND
      have Rd : d ≤ Nat.card (R n p r hrnz hp hnnoprdivs) := by sorry -- d > (log n )^2, the order of n mod r by assumption? (thats what is in the text)
      have RB : ⌊√ ↑ (Nat.card (R n p r hrnz hp hnnoprdivs)) * Real.logb 2 n⌋ < Nat.card (R n p r hrnz hp hnnoprdivs)  := by sorry -- i guess the result above?
      have : (n : ℝ)^(√ ↑ (Nat.card (R n p r hrnz hp hnnoprdivs)))-1 < Nat.card (G n p r hrnz) := by sorry -- lemma 43

      sorry

    . intro nprime
      constructor
      . sorry
      constructor
      . sorry
      . sorry

-- this is in mathlib: Nat.Prime.dvd_choose_pow_iff
theorem n_choose_k (p : ℕ) (k : ℕ) (hk1 : k < p) (hk2 : k > 0) (hp : Nat.Prime p)
  : p ∣ p.choose k
  := by
    have h := (Nat.Prime.dvd_choose_pow_iff (n := 1) (k := k) (p := p) hp).mpr
    -- Nat.Prime.dvd_choose_self
    rw [pow_one] at h
    have h2 : k ≠ 0 ∧ k ≠ p := by
      constructor
      exact Nat.not_eq_zero_of_lt hk2
      exact Nat.ne_of_lt hk1
    exact h h2


lemma todo (n : ℕ) (hn : ¬ Nat.Prime n) : ∃ (p : ℕ), Nat.Prime p ∧ multiplicity p n ≥ 1 := by
  #check WfDvdMonoid.exists_irreducible_factor (α := ℕ) (a := n)
  -- hn seems to be unnecessary
  -- and of course n cannot be 0 or 1.
  sorry

-- proof based on: https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf
section
  open Polynomial
  -- Will fix this later



  theorem primality (n : ℕ) (hn : n ≥ 2) (a : ZMod n) (coprime : Invertible a)
    : Nat.Prime n ↔ (X + C a)^n = X^n + C a
    := by
      let R := Polynomial (ZMod n)
      let g := (X + C a)^n - (X^n + C a)
      have hg : g = ∑ i ∈ Finset.range (n-1), monomial (i+1) (↑ (n.choose (i+1))) := by
        unfold g
        rw [add_pow]
        sorry
      constructor
      . -- if n is prime, prove the equality holds
        intro nprime
        have h : ∀ i ∈ Finset.range (n-1), (↑ (n.choose (i + 1))) = (0 : ZMod n) := by
          intro i hi
          have hh : i < n-1 := Finset.mem_range.mp hi
          have : n ∣ n.choose (i+1) := n_choose_k n (i+1) (Nat.add_lt_of_lt_sub hh) (Nat.zero_lt_succ i) nprime
          refine (ZMod.natCast_zmod_eq_zero_iff_dvd (n.choose (i + 1)) n).mpr this
        have h2 : ∀ i ∈ Finset.range (n-1), (monomial (i+1) ↑(n.choose (i + 1))) = (0 : R) := by
          intro i hi
          apply (monomial_eq_zero_iff (↑(n.choose (i + 1)) : ZMod n) (i + 1)).mpr
          exact h i hi
        have h3 := Finset.sum_eq_zero h2
        have h4 : g = 0 := by rw [h3] at hg; exact hg
        exact sub_eq_zero.mp h4
      . -- if n is not prime, prove the equality does not hold
        contrapose
        intro hnnotprime
        obtain ⟨q, qprime, hq⟩ := todo n hnnotprime
        let k := multiplicity q n
        have h2 : q^k ∣ n := pow_multiplicity_dvd q n
        have h3 : ¬(q^(k+1) ∣ (n.choose q)) := by
          apply FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt
          . apply Nat.finiteMultiplicity_iff.mpr
            constructor
            exact Nat.Prime.ne_one qprime
            refine Nat.choose_pos ?_
            have hh : q ∣ n := by
              have : q ∣ q^k := by refine dvd_pow_self q (Nat.not_eq_zero_of_lt hq)
              exact Trans.trans this h2
            have hh2 : n ≠ 0 := by exact Nat.not_eq_zero_of_lt hn
            refine Nat.le_of_dvd ?_ hh
            exact Nat.zero_lt_of_ne_zero hh2
          . sorry
        have h4 : g.coeff q ≠ 0 := sorry
        intro equal
        have h5 : g = 0 := sub_eq_zero_of_eq equal
        have h6 : (0 : R).coeff q = 0 := rfl
        have := congrArg (λ p ↦ p.coeff q) h5
        simp [coeff_zero] at this
        exact h4 this
