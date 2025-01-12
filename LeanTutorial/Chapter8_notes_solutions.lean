--- LEAN BOOK CHAPTER 8
import Mathlib

--- For Monoids
-- Monoid for multiplicative notation
#check Monoid
-- Monoid for additive notation
#check AddMonoid
-- CommMonnoid for commutative monoid
#check CommMonoid
-- Composition of maps (morphisms)
example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f
#check MonoidHom.comp

--- Groups are monoids that have inverses
-- both group and ring tactic are used to prove all the identities in rings/groups
-- abel are for commutative additive groups to prove identities
-- some other properties/functions in the book

--- Subgroups
-- subgroup G vs IsSubgroup H??

--- Exercises Subgroups
def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    use 1
    rw[mul_one]
    rw[mul_inv_cancel]
    group
    simp
    apply one_mem
  inv_mem' := by
    dsimp
    intro k k_def
    cases' k_def with h p
    cases' p with a b
    rw[b]
    simp
    use h⁻¹
    group
    simp
    exact a
  mul_mem' := by
    dsimp
    intro a
    intro b
    intro a_def
    intro b_def
    use a*b, H.mul_mem a_def b_def
    sorry

example (P Q R : Prop) : (P → (Q ∧ R) → S) := by
    intro hP
    intro h
    cases' h with hQ hR

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h
section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
    sorry

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  sorry

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  sorry

-- Pushing a subgroup along one homomorphism and then another is equal to
-- pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
  sorry

end exercises
