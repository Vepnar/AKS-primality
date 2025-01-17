import Mathlib
import lemma_41

open Polynomial

def bigF (p : ℕ) (h : Polynomial (ZMod p))
:= AdjoinRoot h
