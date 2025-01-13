import Mathlib
open Polynomial

noncomputable def ZtoZp (p : ℕ ) := Polynomial.map (Int.castRingHom (ZMod p))
#check ZtoZp 5 (6*X^5)

-- def extracth

def bigF (p : ℕ ) (h : Polynomial (ZMod p))
:= AdjoinRoot h

-- putting in the database that lean has the fact that it is a field
-- haveI for inst
-- let for functions
-- have for proof of prop
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] (h : Polynomial (ZMod p)) [Fact (Irreducible h)] : Field (bigF p h) := by
  exact AdjoinRoot.instField

-- Polynomial.factor
-- Polynomial.irreducible_factor
-- Polynomial.cyclotomic
-- reducing polynomials over Z to Z/p

-- map cyclotomic polynomial to polynomial over Z mod p

-- first take the rth cyclotomic polynomial of x^r-1
-- then map it to Zp
-- then extract an irreducible factor


-- now find a function that sends pol in Z to Zp
-- polynomial

-- morphism from r to s -- each coefficient of the polynomial is mapped through morphism

section
  variable {p r : ℕ} [Fact (Nat.Prime p)] {h : Polynomial (ZMod p)} [Fact (Irreducible h)] {h_divides : h ∣ X^r - 1} {A : ℕ}

  noncomputable def f : Polynomial (ZMod p) := X^r - 1

  noncomputable def α : AdjoinRoot (f (p := p) (r := r)) := AdjoinRoot.root f

  noncomputable def H : Submonoid (AdjoinRoot (R := ZMod p) (X^r - 1))
    := Submonoid.closure
        {h | ∃ (n : ℕ), n ≤ A ∧ h = AdjoinRoot.of (X^r-1) (↑ n)}

  noncomputable def G : Submonoid (bigF p h) := Submonoid.map (AdjoinRoot.algHomOfDvd h_divides) (H (A := A))

  lemma helper : (aeval ((AdjoinRoot.root (f (p := p) (r := r))) ^ k)) (f (p := p) (r := r)) = 0 := by
    let f : Polynomial (ZMod p) := X^r - 1
    let α := AdjoinRoot.root f
    show (aeval (α ^ k)) f = 0
    have : (aeval (α ^ k)) f = (α ^ k) ^ r - 1 := by
      unfold f
      simp only [map_sub, AdjoinRoot.mk_X, map_pow, aeval_X, map_one]

    rw [this, ← pow_mul, mul_comm k r, pow_mul]

    have : α ^ r = 1 := by
      have : α ^ r - 1 = 0 := by calc
        α ^ r - 1 = IsAdjoinRoot.map (AdjoinRoot.isAdjoinRoot f) f := rfl
        _         = 0 := by simp only [this, AdjoinRoot.isAdjoinRoot_map_eq_mk, AdjoinRoot.mk_self]
      have : α ^ r - 1 + 1 = 0 + 1 := congrArg (. + 1) this
      simp only [sub_add_cancel, zero_add] at this
      assumption
    simp [this]

  def S : Set ℕ := {
    k | ∀ g ∈ H (p := p) (r := r) (A := A),
      g^k = AdjoinRoot.liftHom (f) (α^k) helper g
    }

  def stmt1 (g : bigF p h) (hg : g ∈ G (p := p) (r := r) (A := A) (h_divides := h_divides)) : g ≠ 0 :=
    by sorry




example : ℤ →+* (ZMod p) := by exact Int.castRingHom (ZMod p)


#check Int.castRingHom (ZMod 3)
