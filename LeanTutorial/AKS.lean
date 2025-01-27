import Mathlib
import LeanTutorial.basic
import LeanTutorial.lowerBoundG
import LeanTutorial.upperBoundG

theorem AKS (n r : ℕ) (hn: n ≥ 2) (rpos : 0 < r) (hr: r < n) (hnorder : orderOf (↑ n : ZMod r) > ⌊(Real.logb 2 n) ^ 2 ⌋₊):
    (¬is_perfect_power n ∧ no_prime_divisors_below n r
    ∧ (∀ a ∈ Finset.range (A n r + 1), (α n r + ↑ a)^n = α n r^n + ↑ a)) ↔ Nat.Prime n := by
    have hrnz : r ≠ 0 := (ne_of_lt rpos).symm
    constructor
    . intro ⟨ hnnotperfpow, hnnoprdivs, last_prop⟩
      by_contra nnotprime
      let p : ℕ := Nat.minFac n
      have hp : p ∣ n := Nat.minFac_dvd n
      haveI : Fact (p.Prime) := Fact.mk (Nat.minFac_prime (ne_of_lt hn).symm)

      have lowerboundG : Nat.card (G n p r hrnz) > (n : ℝ)^(Real.sqrt (Nat.card (R n p r hrnz hp hnnoprdivs))) - 1
        := by
        sorry
        --lower_bound_G n p r hrnz hp hnnoprdivs

      have upperboundG : Nat.card (G n p r hrnz) ≤ (n : ℝ)^(Real.sqrt (Nat.card (R n p r hrnz hp hnnoprdivs))) - 1
        := sorry
        -- upper_bound_G n p r hrnz hp hnnoprdivs

      have : (Nat.card (G n p r hrnz) : ℝ) < Nat.card (G n p r hrnz) := lt_of_le_of_lt upperboundG lowerboundG

      exact lt_irrefl (Nat.card (G n p r hrnz) : ℝ) this

    . intro nprime
      haveI : Fact (n.Prime) := Fact.mk nprime
      constructor
      . by_contra npp
        obtain ⟨k, j, k1, j1, npp⟩ := npp
        have k_lt_n := lt_self_pow₀ k1 j1
        rw[npp] at k_lt_n
        have : k ∣ n := by
          rw[← npp, dvd_iff_exists_eq_mul_left]
          use k ^ (j-1)
          rw[Nat.pow_pred_mul]
          exact le_trans (by norm_num) j1
        have := (Nat.dvd_prime_two_le nprime k1).mp this
        exact ne_of_lt k_lt_n this
      constructor
      . unfold no_prime_divisors_below
        simp
        intro p hp hhp
        rw[Nat.dvd_prime_two_le nprime (Nat.Prime.two_le hp)] at hhp
        rw[hhp]
        exact hr
      . intro a _ -- assumption on a is unnecessary
        haveI := instCharPAdjoinRootF n r hrnz
        simp [add_pow_char (α n r) (↑ a) n]
        calc
            (a : AdjoinRoot (f n r))^n = (AdjoinRoot.of (f n r) (a : ZMod n))^n := by rw [map_natCast]
            _ = AdjoinRoot.of (f n r) ((a : ZMod n)^n) := by rw[map_pow]
            _ = AdjoinRoot.of (f n r) (a : ZMod n) := by simp only [ZMod.pow_card, map_natCast]
            _ = AdjoinRoot.of (f n r) a := by rw [map_natCast]
