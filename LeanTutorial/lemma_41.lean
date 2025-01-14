import Mathlib
open Polynomial

noncomputable def ZtoZp (p : ℕ) := Polynomial.map (Int.castRingHom (ZMod p))
#check ZtoZp 5 (6*X^5)

noncomputable def extracth (r : ℕ) := ZtoZp r (Polynomial.cyclotomic r ℤ)

def bigF (p : ℕ) (h : Polynomial (ZMod p))
:= AdjoinRoot h

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] (h : Polynomial (ZMod p)) [Fact (Irreducible h)] : Field (bigF p h) := by
  exact AdjoinRoot.instField


-- ASK ALAIN: variables?
section
  variable {p r : ℕ} [Fact (Nat.Prime p)] {h : Polynomial (ZMod p)} [Fact (Irreducible h)] {h_divides : h ∣ X^r - 1} {A : ℕ}

  noncomputable def f : Polynomial (ZMod p) := X^r - 1

  noncomputable def α : AdjoinRoot (f (p := p) (r := r)) := AdjoinRoot.root f

  noncomputable def H : Submonoid (AdjoinRoot (R := ZMod p) (X^r - 1))
    := Submonoid.closure
        {h | ∃ (n : ℕ), n ≤ A ∧ h = α + AdjoinRoot.of f (↑ n)}

  noncomputable def G : Submonoid (bigF p h) := Submonoid.map (AdjoinRoot.algHomOfDvd h_divides) (H (A := A))
  -- TODO: prove G is a subgroup (enough to show that 0 ∉ G)
  -- Show that f(X^k) = 0, needed for the definition of S (for evaluation of f at X^k to be well-defined)
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

lemma lemma41 (a b : ℕ)
  (sha : a ∈ S (p := p) (A := A) (r := r))
  (shb : b ∈ S (p := p) (A := A) (r := r))
  : a*b ∈ S (p := p) (A := A) (r := r) := by
  show ∀ g ∈ H (p := p) (r := r) (A := A),
      g^(a*b) = AdjoinRoot.liftHom _ (α^(a*b)) helper g

  intro g hg
  rw [pow_mul, sha, shb]

  -- ugly part to make sure sha and shb actually apply
  -- ASK ALAIN
  rotate_right 1
  trivial

  rotate_right 1
  rw [← sha]
  apply pow_mem
  trivial
  trivial

  -- proof of what we actually care about
  let φ := (AdjoinRoot.liftHom f (α ^ b) helper).comp (AdjoinRoot.liftHom (f (p := p) (r := r)) (α ^ a) helper)
  let ψ := (AdjoinRoot.liftHom (f (p := p) (r := r)) (α ^ (a * b)) helper)

  have : φ = ψ := AdjoinRoot.algHom_ext (by calc
    _ = (AdjoinRoot.liftHom f (α ^ b) helper) (AdjoinRoot.liftHom (f (p := p) (r := r)) (α ^ a) helper (AdjoinRoot.root f)) := rfl
    _ = (AdjoinRoot.liftHom f (α ^ b) helper) (α^a) := by (rw[AdjoinRoot.liftHom_root (a := α ^ a) ]; )
    _ = (AdjoinRoot.liftHom f (α ^ b) helper α)^a := by (simp[AdjoinRoot.liftHom_root]; )
    _ = (AdjoinRoot.liftHom f (α ^ b) helper (AdjoinRoot.root f))^a := rfl
    _ = (α ^ b)^a := by rw[AdjoinRoot.liftHom_root]
    _ = α^(b*a) := by simp[pow_mul]
    _ = α^(a*b) := by simp[mul_comm]
    _ = (AdjoinRoot.liftHom f (α ^ (a * b)) helper) (AdjoinRoot.root _) := by simp only [AdjoinRoot.liftHom_root]
    _ = ψ (AdjoinRoot.root f) := rfl
    )

  calc
    _ = φ g := rfl
    _ = ψ g := by rw [this]
    _ = _ := rfl




lemma lemma42 (a b : ℕ)
  (ha : a ∈ S (p := p) (A := A) (r := r))
  (hb : b ∈ S (p := p) (A := A) (r := r))
  (hab : a = b % r) :
  a ≡ b [MOD Nat.card (G (h:= h) (A:= A) (p:=p) (h_divides := h_divides))] := by
  have : ∀ (g : Polynomial ℤ) (u v : ℤ), u - v ∣ (Polynomial.eval u g) - (Polynomial.eval u g) := by
    exact fun g u v ↦ Int.ModEq.dvd rfl
  let f : Polynomial (ZMod p) := X^r - 1
  let ab : Polynomial (ZMod p) := X^(a-b % r)-1
  have : f ∣ ab := by
    unfold ab
    simp [hab]
  let xaxb : Polynomial (ZMod p) := X^a - X^b
  have : ab ∣ xaxb := by
    unfold xaxb
    unfold ab
    rw [hab]
    simp
    sorry
  sorry
