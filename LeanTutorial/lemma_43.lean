import Mathlib
import LeanTutorial.basic
open Polynomial

variable (p r : ℕ) (hrnz : r ≠ 0) [Fact (Nat.Prime p)] (A : ℕ)

lemma lemma43 (g q : Polynomial (ZMod p)) (hg : AdjoinRoot.mk (h p r) g ∈ Gmonoid p r hrnz A) (hq : AdjoinRoot.mk (h p r) q ∈ Gmonoid p r hrnz A)
  (hmod : AdjoinRoot.mk (h p r) g = AdjoinRoot.mk (h p r) q)
  (hdegg : Polynomial.degree g < R) (hdegq : Polynomial.degree q < R)
  : g = q := by
  let Δ := g - q
  have hΔmod : ∀ k ∈ S p r A, AdjoinRoot.mk (h p r) (Δ.comp X^k) = 0
  intro X

  --rw [hmod, AdjoinRoot.mk_sub],
  --exact sub_self _, modular equality??
