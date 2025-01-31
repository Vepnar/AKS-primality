import Init.Data.Nat.Log2
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.List.Basic
import Init.PropLemmas
import Mathlib.GroupTheory.OrderOfElement



def rBounds (n : ℕ) : List ℕ :=
  (List.range ((Nat.log2 n)^5+1) ).map (fun i => ((Nat.log2 n)^5 + i))

-- Q₁  Order in what?
theorem prime_in_bounds(n : ℕ) (h₀ : n ≥ 6) : ∃ r ∈ rBounds n, Nat.Prime r ∧ orderOf (↑ n : ZMod r) > (Nat.log2 n)^2 := by
  by_contra h₁
  simp [not_exists_of_forall_not] at h₁
  sorry


def set_between (a b : ℕ ) : Set ℕ :=
