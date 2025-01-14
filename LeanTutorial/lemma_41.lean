import Mathlib
open Polynomial

noncomputable def ZtoZp (p : ℕ) := Polynomial.map (Int.castRingHom (ZMod p))
#check ZtoZp 5 (6*X^5)

noncomputable def extracth (r : ℕ) := ZtoZp r (Polynomial.cyclotomic r ℤ)

def bigF (p : ℕ) (h : Polynomial (ZMod p))
:= AdjoinRoot h

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] (h : Polynomial (ZMod p)) [Fact (Irreducible h)] : Field (bigF p h) := by
  exact AdjoinRoot.instField

section
  variable {p r : ℕ} [Fact (Nat.Prime p)] {h : Polynomial (ZMod p)} [Fact (Irreducible h)] {h_divides : h ∣ X^r - 1} {A : ℕ}

  noncomputable def f : Polynomial (ZMod p) := X^r - 1

  noncomputable def α : AdjoinRoot (f (p := p) (r := r)) := AdjoinRoot.root f

  noncomputable def H : Submonoid (AdjoinRoot (R := ZMod p) (X^r - 1))
    := Submonoid.closure
        {h | ∃ (n : ℕ), n ≤ A ∧ h = α + AdjoinRoot.of f (↑ n)}

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
      g^k = AdjoinRoot.liftHom f (α^k) helper g
    }

  def stmt1 (g : bigF p h) (hg : g ∈ G (p := p) (r := r) (A := A) (h_divides := h_divides)) : g ≠ 0 :=
    by sorry




example : ℤ →+* (ZMod p) := by exact Int.castRingHom (ZMod p)


#check Int.castRingHom (ZMod 3)

#check H

lemma lemma41 (a b : ℕ) (ha : a > 0) (hb : b > 0)
  (sha : a ∈ S (p := p) (A := A) (r := r))
  (shb : b ∈ S (p := p) (A := A) (r := r))
  : a*b ∈ S (p := p) (A := A) (r := r) := by
  sorry


lemma lemma42 (a b : ℕ)
  (ha : a ∈ S (p := p) (A := A) (r := r))
  (hb : b ∈ S (p := p) (A := A) (r := r))
  (hab : a = b % r) :
  a ≡ b [MOD Nat.card (G (h:= h) (A:= A) (p:=p) (h_divides := h_divides))] := by
  sorry
