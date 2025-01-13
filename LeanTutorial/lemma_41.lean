import Mathlib

def irrh (h : Polynomial (ZMod p)) := sorry

def bigF (p : ℕ ) (h : Polynomial (ZMod p))
:= AdjoinRoot h

-- putting in the database that lean has the fact that it is a field
-- haveI for inst
-- let for functions
-- have for proof of prop
noncomputable instance (p : ℕ ) [Fact (Nat.Prime p)] (h : Polynomial (ZMod p)) [Fact (Irreducible h)] : Field (bigF p h) := by
  exact AdjoinRoot.instField

-- Polynomial.factor
-- Polynomial.irreducible_factor
-- Polynomial.cyclotomic
-- reducing polynomials over Z to Z/p
