import Mathlib

noncomputable def φ : Polynomial (ZMod p) →+* AdjoinRoot (f p r) :=
  AdjoinRoot.mk (f p r)

  lemma pinS : p ∈ S p r A := by
  intro g hg

  have (q : (ZMod p)[X]) : q ^ p = q.comp (X ^ p) := by
    rw [← Polynomial.expand_char, ZMod.frobenius_zmod]
    simp
    exact Polynomial.expand_eq_comp_X_pow p

  have := fun q => congrArg (φ p r) (this q)
  unfold φ at this
  simp at this
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective g

  have := this q

  rw [hq] at this
  rw[this]

  calc
  _ = (AdjoinRoot.mk (f p r)) (q.eval₂ C (X ^ p)) := by rfl
  _ = (AdjoinRoot.mk (f p r)) (q.eval₂ C (X ^ p)) := by rfl
  _ = (AdjoinRoot.liftHom (f p r) (AdjoinRoot.root (f _ _) ^ p) (helper _ _)) g := by sorry
  _ = (AdjoinRoot.liftHom (f p r) (AdjoinRoot.root (f _ _) ^ p) (helper _ _)) g := by rfl
  _ = _ := by rfl
