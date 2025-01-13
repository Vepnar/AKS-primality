import Mathlib
open Polynomial

noncomputable def ZtoZp (p : ℕ ) := Polynomial.map (Int.castRingHom (ZMod p))
#check ZtoZp 5 (6*X^5)

def extracth

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

-- map cyclotomic polynomial to polynomial over Z mod p

-- first take the rth cyclotomic polynomial of x^r-1
-- then map it to Zp
-- then extract an irreducible factor


-- now find a function that sends pol in Z to Zp
-- polynomial

-- morphism from r to s -- each coefficient of the polynomial is mapped through morphism

example : ℤ →+* (ZMod p) := by exact Int.castRingHom (ZMod p)


#check Int.castRingHom (ZMod 3)
