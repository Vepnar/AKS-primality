import Mathlib
import LeanTutorial.basic
import LeanTutorial.lemma_41
open Polynomial

variable (n p r : ℕ) (hrnz : r ≠ 0) [pprime : Fact (Nat.Prime p)]
  (hp : p ∣ n) (hnnoprdivs : no_prime_divisors_below n r) (hnnotperfpow : ¬ is_perfect_power n) (hnodd : Odd n) (hn_gt_one : n > 1)
  (childs_binomial_theorem : ∀ a ∈ Finset.range (A n r + 1),
    (α p r + ↑ a)^n = α p r^n + ↑ a)
  (hordern : orderOf (↑ n : ZMod r) > ⌊(Real.logb 2 n) ^ 2 ⌋₊)

lemma poly_div_lemma {R : Type*} [CommRing R] (a b c : ℕ)
  (modeq : a ≡ b [MOD c]) : (X : R[X])^c - 1 ∣ X^b - X^a := by
  wlog hba : a ≤ b
  . have fact : b ≤ a := Nat.le_of_not_ge hba
    have := this (R := R) b a c modeq.symm fact
    exact dvd_sub_comm.mp this
  have : (X : R[X])^b - X^a = (X^(b-a) - 1) * X^a := by
    have : (b - a) + a = b := by exact Nat.sub_add_cancel hba
    rw [mul_sub_right_distrib, ← pow_add, this, one_mul]
  rw [this]
  apply dvd_mul_of_dvd_left
  obtain ⟨d, hd⟩ := (Nat.modEq_iff_dvd' hba).mp modeq
  have := sub_dvd_pow_sub_pow ((X : R[X])^c) 1 d
  simp only [← pow_mul, ← hd, one_pow] at this
  exact this

include hn_gt_one childs_binomial_theorem in
lemma idkhowtonamethis (a b : ℕ) (ha : a ∈ S n p r) (eqmod : a ≡ b [MOD n^d n r-1])
  (hanz : a ≠ 0) (hbnz : b ≠ 0)
  : b ∈ S n p r := by
  have hrdiv : r ∣ n^d n r - 1 := by
    suffices (n : ZMod r)^d n r - 1 = 0 by
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ r).mp
      rw[← this]
      trans ↑(n^d n r) - 1
      . refine Nat.cast_pred (Nat.pow_pos ?_)
        linarith
      . rw [Nat.cast_pow]
    unfold d
    simp [pow_orderOf_eq_one]

  have step₁ : (X : (ZMod p)[X])^r - 1 ∣ X^(n^d n r - 1) - 1 :=
    poly_div_lemma 0 (n^d n r -1) r hrdiv.zero_modEq_nat

  have : (X : (ZMod p)[X])^(n^d n r - 1) - 1 ∣ X^b - X^a := poly_div_lemma _ _ _ eqmod

  have halphaab : α p r ^ a = α p r ^ b := by
    suffices AdjoinRoot.mk (f p r) (X^a) = AdjoinRoot.mk (f p r) (X^b) by
      simp only [map_pow, AdjoinRoot.mk_X] at this
      exact this
    symm
    apply AdjoinRoot.mk_eq_mk.mpr
    unfold f
    trans
    . exact step₁
    . exact this

  have (g : (ZMod p)[X][X]) : X^b - X^a ∣ g.eval (X^b) - g.eval (X^a) := sub_dvd_eval_sub (X ^ b) (X ^ a) g

  have : n^d n r ∈ S n p r := pow_in_S n p r n (d n r) (ninS n p r childs_binomial_theorem)

  have step₂ (g : AdjoinRoot (f p r)) (hg : g ∈ H n p r) : g^n^d n r = g.liftHom (f _ _) (α _ _^n^d n r) (helper _ _) := this _ hg

  have : α p r^n^d n r = α p r := by
    suffices : AdjoinRoot.mk (f p r) (X^n^d n r) = AdjoinRoot.mk (f _ _) X
    . simp only [map_pow, AdjoinRoot.mk_X] at this
      exact this
    . apply AdjoinRoot.mk_eq_mk.mpr
      unfold f
      have := poly_div_lemma (R := ZMod p) 1 (n^d n r) r (by
        apply (Nat.modEq_iff_dvd' _).mpr
        exact hrdiv
        exact one_le_pow₀ (le_of_lt hn_gt_one)
      )
      rw [pow_one] at this
      exact this

  have g_pow_n_d_eq_g (g : AdjoinRoot (f p r)) (hg : g ∈ H n p r) : g^n^d n r = g := by
    rw [step₂ _ hg]
    simp_rw[this]
    unfold α
    have := AdjoinRoot.liftHom_eq_algHom (f p r) (AlgHom.id _ (AdjoinRoot (f p r)))
    simp only [AlgHom.coe_id, id_eq] at this
    rw [this]
    simp only [AlgHom.coe_id, id_eq]

  have cancelgs (g : AdjoinRoot (f p r)) (hg : g ∈ H n p r) : ∀ (c : ℕ), g * (g^(n^d n r - 1))^c = g := by
    intro c
    induction c with
    | zero => ring
    | succ c' ih =>
      rw[add_comm c', pow_add, pow_one, ← mul_assoc, mul_comm g]
      nth_rw 2 [← pow_one g]
      rw[← pow_add, Nat.sub_add_cancel (one_le_pow₀ (le_of_lt hn_gt_one)),
        g_pow_n_d_eq_g g hg]
      exact ih

  have (g : AdjoinRoot (f p r)) (hg : g ∈ H n p r) : g^b = g^a := by
    rcases le_total a b with hab | hba
    . obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hab).mp eqmod
      have habcancel : b - a + a = b := Nat.sub_add_cancel hab
      have ha1cancel : a - 1 + 1 = a := Nat.sub_add_cancel (Nat.zero_lt_of_ne_zero hanz)
      have := calc
        g^b = g^(b - a + a) := by rw[habcancel]
        _   = g^a * g^(b-a) := by ring
        _   = g^a * g^((n^d n r-1)*c) := by rw[hc]
        _   = g^a * (g^(n^d n r-1))^c := by ring
        _   = g^(a-1+1) * (g^(n^d n r-1))^c := by rw[ha1cancel]
        _   = g^(a-1) * (g * (g^(n^d n r-1))^c) := by ring
      rw[this, cancelgs g hg]
      nth_rw 2 [← pow_one g]
      rw[← pow_add, ha1cancel]
    . obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hba).mp eqmod.symm
      have habcancel : a - b + b = a := Nat.sub_add_cancel hba
      have ha1cancel : b - 1 + 1 = b := Nat.sub_add_cancel (Nat.zero_lt_of_ne_zero hbnz)
      have := calc
        g^a = g^(a - b + b) := by rw[habcancel]
        _   = g^b * g^(a-b) := by ring
        _   = g^b * g^((n^d n r-1)*c) := by rw[hc]
        _   = g^b * (g^(n^d n r-1))^c := by ring
        _   = g^(b-1+1) * (g^(n^d n r-1))^c := by rw[ha1cancel]
        _   = g^(b-1) * (g * (g^(n^d n r-1))^c) := by ring
      rw[this, cancelgs g hg]
      nth_rw 3 [← pow_one g]
      rw[← pow_add, ha1cancel]

  intro g hg
  calc
  g^b = g^a := this g hg
  _ = g.liftHom (f p r) (α p r ^ a) (helper _ _) := ha g hg
  _ = g.liftHom (f p r) (α p r ^ b) (helper _ _) := by simp_rw[halphaab]

lemma how_about_this (a b : ℕ) (ha : a ∣ b) (hb : b ≥ 1) (haineq : a ≥ 3)
  : a.gcd (b-1) = 1 := by
  let c := b/a
  have hc : b = a*c := by exact Eq.symm (Nat.mul_div_cancel' ha)
  have : c ≠ 0 := λ czero ↦ by
    simp_all only [czero,mul_zero,nonpos_iff_eq_zero, one_ne_zero]
  have : c ≥ 1 := Nat.one_le_iff_ne_zero.mpr this
  have : a*(c-1) + a = b := calc
    _ = a * (c - 1 + 1) := by ring
    _ = a * c := by congr; exact Nat.sub_add_cancel this
    _ = b := hc.symm

  have : b-1 = a*(c-1) + a-1 := by congr; exact this.symm
  rw[this]

  have age1 : a ≥ 1 := by linarith

  let a' := a-1
  have ha' : a' + 1 = a := by unfold a'; exact Nat.sub_add_cancel age1
  let a'' := a'-1
  have ha'' : a'' + 1 = a - 1 := by apply Nat.sub_add_cancel; linarith
  calc
  _ = a.gcd ((a * (c - 1) + a - 1) % a) := by rw[← ha', Nat.gcd_add_one, ha', Nat.gcd_comm]
  _ = a.gcd ((a * (c - 1) + (a - 1)) % a) := by rw[Nat.add_sub_assoc age1]
  _ = a.gcd (((a - 1) + a * (c - 1)) % a) := by rw[Nat.add_comm (a * (c-1)) (a-1)]
  _ = a.gcd ((a - 1) % a) := by rw [Nat.add_mul_mod_self_left]
  _ = a.gcd (a - 1) := by congr; exact Nat.self_sub_mod a 1
  _ = (a-1).gcd a := by rw [Nat.gcd_comm]
  _ = (a-1).gcd (a % (a-1)) := by rw[← ha'', Nat.gcd_add_one, ha'', Nat.gcd_comm]
  _ = a'.gcd ((a' + 1) % a') := by unfold a'; rw[ha']
  _ = a'.gcd (1 % a') := by congr 1; exact Nat.add_mod_left _ _
  _ = a'.gcd 1 := by congr; apply Nat.mod_eq_of_lt; linarith
  _ = 1 := by simp only [Nat.gcd_one_right]

include hordern hp hn_gt_one hnodd childs_binomial_theorem in
lemma ndivpinS : n/p ∈ S n p r := by
  let k := n^d n r-1
  let a := n * p^(k.totient - 1)
  let b := n/p
  have hb : b * p = n := Nat.div_mul_cancel hp

  have hanz : a ≠ 0 := Nat.mul_ne_zero
    (ne_of_gt (by linarith))
    (ne_of_gt (one_le_pow₀ (Nat.Prime.one_le pprime.out)))

  have hbnz : b ≠ 0 := by
    intro bzero
    rw [bzero, zero_mul] at hb
    rw [← hb] at hn_gt_one
    contradiction

  have hnpowd : 0 < k := by
    exact Nat.zero_lt_sub_of_lt (n_td_d_gt_one n r hn_gt_one hordern)

  have pkcoprime : Nat.Coprime p k := by
    unfold k
    apply Nat.coprime_iff_gcd_eq_one.mpr
    exact how_about_this p (n ^ d n r)
      (dvd_pow hp (Nat.not_eq_zero_of_lt hordern))
      (one_le_pow₀ (by linarith))
      (pge3 n p hp hnodd)

  have : (a : ZMod k) = b := by
    suffices idk : (a : ZMod k) * p = b * p by
      let pinv := ZMod.inv k p
      have hpinv : p * pinv = 1 := ZMod.coe_mul_inv_eq_one p pkcoprime
      have : ((a : ZMod k) * p) * pinv = (b * p) * pinv := congrArg (. * pinv) idk
      rw [mul_assoc,mul_assoc] at this
      simp only [hpinv, mul_one] at this
      exact this
    unfold a b
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [← Nat.cast_mul (n/p) p, hb, mul_assoc,
      ← Nat.cast_pow, ← Nat.cast_mul (p ^ _) p, ← pow_succ,
      Nat.sub_add_cancel (Nat.totient_pos.mpr hnpowd),
    ]
    have : (p^(k.totient) : ZMod k) = 1 := by
      have : (p^k.totient : ZMod k) = (p : ZMod k)^k.totient := rfl
      have := (ZMod.natCast_eq_natCast_iff (p^k.totient) 1 k).mpr (Nat.ModEq.pow_totient pkcoprime)
      simp only [Nat.cast_pow, Nat.cast_one] at this
      exact this
    simp[this]

  have : ((a : ℤ) : ZMod k) = ((b : ℤ) : ZMod k) := by
    simp only [Int.cast_natCast]
    exact this

  have aequivb_inz : a ≡ b [ZMOD k] := (ZMod.intCast_eq_intCast_iff _ _ _).mp this

  have aequivb : a ≡ b [MOD k] := Int.natCast_modEq_iff.mp aequivb_inz

  have ainS : a ∈ S n p r := by
    unfold a
    apply lemma41 n p r
    . exact ninS n p r childs_binomial_theorem
    . apply pow_in_S n p r
      exact pinS n p r

  exact idkhowtonamethis n p r hn_gt_one childs_binomial_theorem a b ainS aequivb hanz hbnz
