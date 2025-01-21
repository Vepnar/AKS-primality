import Mathlib
import LeanTutorial.basic
open Polynomial

variable (n p r : ℕ) (hrnz : r ≠ 0) [Fact (Nat.Prime p)] (A : ℕ)
lemma lemma41 (a b : ℕ)
  (sha : a ∈ S n p r)  -- make the variables explicit --> ()
  (shb : b ∈ S n p r)
  : a*b ∈ S n p r := by
  show ∀ g ∈ H n p r,
    g^(a*b) = AdjoinRoot.liftHom (f p r) (α p r^(a*b)) (helper p r) g

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
  let φ := (AdjoinRoot.liftHom (f _ _) (α _ _ ^ b) (helper p r)).comp (AdjoinRoot.liftHom (f _ _) (α _ _ ^ a) (helper _ _))
  let ψ := (AdjoinRoot.liftHom (f _ _) (α _ _ ^ (a * b)) (helper p r))

  have : φ = ψ := AdjoinRoot.algHom_ext (by calc
    _ = (AdjoinRoot.liftHom (f _ _) (α _ _ ^ b) (helper _ _)) (AdjoinRoot.liftHom (f _ _) (α _ _ ^ a) (helper p r) (AdjoinRoot.root (f _ _))) := rfl
    _ = (AdjoinRoot.liftHom (f _ _) (α _ _ ^ b) (helper _ _)) (α _ _^a) := by (rw[AdjoinRoot.liftHom_root (a := α _ _ ^ a) ]; )
    _ = (AdjoinRoot.liftHom (f _ _) (α _ _ ^ b) (helper _ _) (α _ _))^a := by (simp[AdjoinRoot.liftHom_root]; )
    _ = (AdjoinRoot.liftHom (f _ _) (α _ _ ^ b) (helper _ _) (AdjoinRoot.root (f _ _)))^a := rfl
    _ = (α _ _ ^ b)^a := by rw[AdjoinRoot.liftHom_root]
    _ = α _ _^(b*a) := by simp[pow_mul]
    _ = α _ _^(a*b) := by simp[mul_comm]
    _ = (AdjoinRoot.liftHom (f _ _) (α _ _ ^ (a * b)) (helper _ _)) (AdjoinRoot.root _) := by simp only [AdjoinRoot.liftHom_root]
    _ = ψ (AdjoinRoot.root (f _ _)) := rfl
    )

  calc
    _ = φ g := rfl
    _ = ψ g := by rw [this]
    _ = _ := rfl

lemma one_in_S : 1 ∈ S n p r
  := by
  intro g hg
  unfold α
  simp only [pow_one]
  have := AdjoinRoot.liftHom_eq_algHom (f p r) (AlgHom.id _ (AdjoinRoot (f p r)))
  simp only [AlgHom.coe_id, id_eq] at this
  rw [this]
  simp only [AlgHom.coe_id, id_eq]

lemma pow_in_S (a b : ℕ) (ha : a ∈ S n p r)
  : a^b ∈ S n p r := by
  induction b with
  | zero => simp; exact (one_in_S _ _ _)
  | succ hb ih => rw[pow_add,pow_one]; exact lemma41 n p r (a^hb) a ih ha
