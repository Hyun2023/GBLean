-- Todo
-- 1. Define Buchberger algorithms in two version, one with FiniteVarPoly, and another just Mvpoly

import Mathlib.Algebra.MvPolynomial.Basic
import GB.Monomial
import GB.Polynomial
import GB.Reduction
import GB.S_Poly

open Monomial

-- Handles MvPolynomial, which operations are noncomputable
section BuchbergerAlgorithm

variable {σ: Type} {R: Type} [DecidableEq σ] [Field R] [DecidableEq R]

def Spoly (f g : MvPolynomial σ R) : MvPolynomial σ R := sorry

def reduction_list (gen: List (MvPolynomial σ R)) (f : MvPolynomial σ R)
  : MvPolynomial σ R := sorry

def reduction_finset (gen: Finset (MvPolynomial σ R)) (f : MvPolynomial σ R)
  : MvPolynomial σ R := reduction_list gen.toList f

section finset

-- argument selected is a list of polynomials which all pairs are reducted
noncomputable def buchberger_step_finset
  (queueing : Finset (MvPolynomial σ R))
  (selected : List (MvPolynomial σ R))
  : Finset (MvPolynomial σ R) :=
  let queue := queueing.toList
  match queue.head? with
  | none => selected.toFinset
  | some f =>
    let fullset := queueing ∪ selected.toFinset
    let reducted := List.map (fun x => reduction_finset fullset (Spoly f x)) selected
    let reducted_no_zero := List.filter (fun x => x != 0) reducted
    buchberger_step_finset (queueing ∪ reducted_no_zero.toFinset) (f :: selected)
  termination_by selected
  decreasing_by
    all_goals simp_wf
    sorry

noncomputable def buchberger_algorithm_finset
  (gen: Finset (MvPolynomial σ R))
  : Finset (MvPolynomial σ R) :=
  let n := gen.card
  if n ≤ 1 then
    gen
  else
    buchberger_step_finset gen []

end finset

-- This algorithm handles FiniteVarPoly, which has computable operation
section list

-- Generate new basis by checking (k, k+1), (k, k+2), ...
-- Get reduction result of Spoly (ith, (i + k + 1)th)
noncomputable def find_new_basis_list
  (gen: List (MvPolynomial σ R))
  (i k: ℕ) -- we will check i-th and (i + k + 1)-th from gen
  : Option (MvPolynomial σ R) :=
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
      let r := reduction_list gen (Spoly gᵢ gₖ)
      if r = 0 then none else some r

-- 'gen' is basis set used to analyze s-polynomials, which size increases monotonically
-- new basis is added to head of basis set which changes index number of rest bases
-- initial argument are given with last two bases
-- total analysis ends when given pair is head of list and one-past the end of list
-- else, in the same situation except i is not in head of list, new pair with initial i is reduced one step is given
-- body of the algorithm first get reduced form of Spoly(i, i + k + 1)
-- if there's no addition of an basis, continue with increased k
-- else, do the same as other branch, but pointing index should updated
noncomputable def buchberger_step_list
  (gen: List (MvPolynomial σ R))
  (i k: ℕ)
  : List (MvPolynomial σ R) :=
  let n := List.length gen
  if n ≤ 1 then
    gen
  else if i = 0 ∧ k ≥ (n - 1) then
    gen
  else if i + k + 2 > n then
    buchberger_step_list gen (i - 1) 0
  else
    let fp := find_new_basis_list gen i 0
    match fp with
    | none => buchberger_step_list gen i (k + 1)
    | some p =>
      buchberger_step_list (p :: gen) (i + 1) (k + 1)
  termination_by i
  decreasing_by
    all_goals simp_wf
    · sorry
    · sorry
    · sorry

noncomputable def buchberger_algorithm_list
  (gen: List (MvPolynomial σ R))
  : List (MvPolynomial σ R) :=
  let n := List.length gen
  if n ≤ 1 then
    gen
  else
    buchberger_step_list gen (n - 0) 0

end list

end BuchbergerAlgorithm

-- Handles FiniteVarPoly, modified MvPolynomial to be computable
section BuchbergerAlgorithm_computable

variable {σ: Type} {R: Type} [DecidableEq σ] [Field R] [DecidableEq R]

def Spoly_computable (f g : FiniteVarPoly σ R) : FiniteVarPoly σ R := sorry

def reduction_computable_list (gen: List (FiniteVarPoly σ R)) (f : FiniteVarPoly σ R)
  : FiniteVarPoly σ R := sorry

def reduction_computable_finset (gen: Finset (FiniteVarPoly σ R)) (f : FiniteVarPoly σ R)
  : FiniteVarPoly σ R := reduction_computable_list gen.toList f

section finset

-- 'gen' is basis set used to analyze s-polynomials, which size increases monotonically
-- new basis is added to head of basis set which changes index number of rest bases
-- initial argument are given with last two bases
-- total analysis ends when given pair is head of list and one-past the end of list
-- else, in the same situation except i is not in head of list, new pair with initial i is reduced one step is given
-- body of the algorithm first get reduced form of Spoly(i, i + k + 1)
-- if there's no addition of an basis, continue with increased k
-- else, do the same as other branch, but pointing index should updated
noncomputable def buchberger_step_computable_finset
  (queueing : Finset (FiniteVarPoly σ R))
  (selected : List (FiniteVarPoly σ R))
  : Finset (FiniteVarPoly σ R) :=
  let queue := queueing.toList
  match queue.head? with
  | none => selected.toFinset
  | some f =>
    let fullset := queueing ∪ selected.toFinset
    let reducted := List.map (fun x => reduction_computable_finset fullset (Spoly_computable f x)) selected
    let reducted_no_zero := List.filter (fun x => x != 0) reducted
    buchberger_step_computable_finset (queueing ∪ reducted_no_zero.toFinset) (f :: selected)
  termination_by selected
  decreasing_by
    all_goals simp_wf
    sorry

noncomputable def buchberger_algorithm_computable_finset
  (gen: Finset (FiniteVarPoly σ R))
  : Finset (FiniteVarPoly σ R) :=
  let n := gen.card
  if n ≤ 1 then
    gen
  else
    buchberger_step_computable_finset gen []

end finset

-- This algorithm handles FiniteVarPoly, which has computable operation
section list

-- Generate new basis by checking (k, k+1), (k, k+2), ...
-- Get reduction result of Spoly (ith, (i + k + 1)th)
def find_new_basis_computable_list
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
      let r := reduction_computable_list gen (Spoly_computable gᵢ gₖ)
      if r = 0 then none else some r

-- 'gen' is basis set used to analyze s-polynomials, which size increases monotonically
-- new basis is added to head of basis set which changes index number of rest bases
-- initial argument are given with last two bases
-- total analysis ends when given pair is head of list and one-past the end of list
-- else, in the same situation except i is not in head of list, new pair with initial i is reduced one step is given
-- body of the algorithm first get reduced form of Spoly(i, i + k + 1)
-- if there's no addition of an basis, continue with increased k
-- else, do the same as other branch, but pointing index should updated
def buchberger_step_computable_list
  (gen: List (FiniteVarPoly σ R))
  (i k: ℕ)
  : List (FiniteVarPoly σ R) :=
  let n := List.length gen
  if n ≤ 1 then
    gen
  else if i = 0 ∧ k ≥ (n - 1) then
    gen
  else if i + k + 2 > n then
    buchberger_step_computable_list gen (i - 1) 0
  else
    let fp := find_new_basis_computable_list gen i 0
    match fp with
    | none => buchberger_step_computable_list gen i (k + 1)
    | some p =>
      buchberger_step_computable_list (p :: gen) (i + 1) (k + 1)
  termination_by i
  decreasing_by
    all_goals simp_wf
    · sorry
    · sorry
    · sorry

def buchberger_algorithm_computable_list
  (gen: List (FiniteVarPoly σ R))
  : List (FiniteVarPoly σ R) :=
  let n := List.length gen
  if n ≤ 1 then
    gen
  else
    buchberger_step_computable_list gen (n - 0) 0

end list

end BuchbergerAlgorithm_computable
