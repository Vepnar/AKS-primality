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
    cases' a_def with a1 a2
    cases' a2 with c1 c2
    intro b_def
    cases' b_def with b1 b2
    cases' b2 with d1 d2
    rw[c2]
    rw[d2]
    simp
    apply mul_mem
    exact c1
    exact d1
