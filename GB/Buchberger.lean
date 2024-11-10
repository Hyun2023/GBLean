-- Todo
-- 1. Define Buchberger algorithms as Lean function
-- 2. Prove termination and correctness

import Mathlib.Algebra.MvPolynomial.Basic
import GB.Monomial
import GB.Polynomial
import GB.Reduction
import GB.S_Poly

open Monomial

section BuchbergerAlgorithm

variable {σ: Type} {R: Type} [DecidableEq σ] [Field R] [DecidableEq R]

-- Generate new basis by checking (k, k+1), (k, k+2), ...
def find_new_basis
  (gen: List (FiniteVarPoly σ R))
  (i k: ℕ) -- we will check i-th and (i + k + 1)-th from gen
  : Option (FiniteVarPoly σ R) :=
  let n := List.length gen
  if k = 0 ∨ i ≥ n ∨ i + k + 1 ≥ n then
    none
  else
    match List.drop i gen with
    | [] => none
    | _ :: [] => none
    | gᵢ :: gen' =>
      match List.drop k gen' with
      | [] => none
      | gₖ :: _ =>
      let r := red_comp_list gen (S gᵢ gₖ)
      if r = 0 then none else some r

def buchberger_algorithm_list
  (gen: List (FiniteVarPoly σ R))
  (nonzero_all: ∀ p ∈ gen, p ≠ 0)
  : List (FiniteVarPoly σ R) :=
  sorry

def buchberger_algorithm
  [DecidableEq R]
  (gen: Finset (FiniteVarPoly σ R))
  (nonzero_all: ∀ p ∈ gen, p ≠ 0)
  : Finset (FiniteVarPoly σ R) :=
  have nz_list: ∀ p ∈ gen.toList, p ≠ 0 := by
    intro p pH
    apply nonzero_all
    exact Finset.mem_toList.mp pH
  (buchberger_algorithm_list gen.toList nz_list).toFinset

end BuchbergerAlgorithm
