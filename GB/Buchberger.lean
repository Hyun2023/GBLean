-- Todo
-- 1. Define Buchberger algorithms in two version, one with FiniteVarPoly, and another just Mvpoly

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.Basic
import GB.Monomial
import GB.Polynomial
import GB.Reduction
import GB.S_Poly

open Monomial

-- Handles MvPolynomial, which operations are noncomputable
section BuchbergerAlgorithm

variable {σ: Type} {R: Type}
[DecidableEq σ]
[Field R]
[DecidableEq R]
[LinearOrder σ]

def Spoly (f g : MvPolynomial σ R) : MvPolynomial σ R := sorry

def s_red (p q : MvPolynomial σ R) (F : Finset (MvPolynomial σ R)) (F_nonzero : ∀ f ∈ F, f ≠ 0): MvPolynomial σ R :=
  ((Spoly p q).multidiv F F_nonzero).snd

-- def reduction_list (gen: List (MvPolynomial σ R)) (f : MvPolynomial σ R)
--   : MvPolynomial σ R := sorry

-- def reduction_finset (gen: Finset (MvPolynomial σ R)) (f : MvPolynomial σ R)
--   : MvPolynomial σ R := reduction_list gen.toList f

section finset

noncomputable def buchberger_step
  (pair_list :  List (MvPolynomial σ R × MvPolynomial σ R))
  (G_queue : Finset (MvPolynomial σ R))
  (G' : Finset (MvPolynomial σ R)) (G'_nonzero : ∀ g ∈ G', g ≠ 0)
  : Finset (MvPolynomial σ R) :=
  match pair_list with
  | [] => G_queue
  | (p,q) :: rem =>
    if p = q then
      buchberger_step rem G_queue G' G'_nonzero
    else
      let S := s_red p q G' G'_nonzero
      if S = 0 then
        buchberger_step rem G_queue G' G'_nonzero
      else
        buchberger_step rem (G_queue ∪ {S}) G' G'_nonzero

noncomputable def buchberger_algorithm
  (F : Finset (MvPolynomial σ R))
  : Finset (MvPolynomial σ R) :=
  if F.card ≤ 1 then
    F
  else
    let G := F.filter (fun p => p ≠ 0)
    have G_nonzero : ∀ g ∈ G, g ≠ 0 := by {intros g gin; exact (Finset.mem_filter.mp gin).2 }
    let G_new := buchberger_step (G.product G).toList G G (G_nonzero)
    if G_new = G then
      G_new
    else
      buchberger_step (G_new.product G_new).toList G_new G_new (sorry)



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
  (G: List (MvPolynomial σ R))
  (i k: ℕ)
  : List (MvPolynomial σ R) :=
  let n := G.length
  if G.length ≤ 1 then
    G
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
  (F: List (MvPolynomial σ R))
  : List (MvPolynomial σ R) :=
  -- let n := F.length

  if F.length <=1 then
    F
  else
    buchberger_step_list F (n - 0) 0

end list

end BuchbergerAlgorithm



-- We do not use FiniteVarPoly now. Followings may be used in future.


-- -- Handles FiniteVarPoly, modified MvPolynomial to be computable
-- section BuchbergerAlgorithm_computable

-- variable {σ: Type} {R: Type} [DecidableEq σ] [Field R] [DecidableEq R]

-- def Spoly_computable (f g : FiniteVarPoly σ R) : FiniteVarPoly σ R := sorry

-- def reduction_computable_list (gen: List (FiniteVarPoly σ R)) (f : FiniteVarPoly σ R)
--   : FiniteVarPoly σ R := sorry

-- def reduction_computable_finset (gen: Finset (FiniteVarPoly σ R)) (f : FiniteVarPoly σ R)
--   : FiniteVarPoly σ R := reduction_computable_list gen.toList f

-- section finset

-- -- 'gen' is basis set used to analyze s-polynomials, which size increases monotonically
-- -- new basis is added to head of basis set which changes index number of rest bases
-- -- initial argument are given with last two bases
-- -- total analysis ends when given pair is head of list and one-past the end of list
-- -- else, in the same situation except i is not in head of list, new pair with initial i is reduced one step is given
-- -- body of the algorithm first get reduced form of Spoly(i, i + k + 1)
-- -- if there's no addition of an basis, continue with increased k
-- -- else, do the same as other branch, but pointing index should updated
-- noncomputable def buchberger_step_computable_finset
--   (queueing : Finset (FiniteVarPoly σ R))
--   (selected : List (FiniteVarPoly σ R))
--   : Finset (FiniteVarPoly σ R) :=
--   let queue := queueing.toList
--   match queue.head? with
--   | none => selected.toFinset
--   | some f =>
--     let fullset := queueing ∪ selected.toFinset
--     let reducted := List.map (fun x => reduction_computable_finset fullset (Spoly_computable f x)) selected
--     let reducted_no_zero := List.filter (fun x => x != 0) reducted
--     buchberger_step_computable_finset (queueing ∪ reducted_no_zero.toFinset) (f :: selected)
--   termination_by selected
--   decreasing_by
--     all_goals simp_wf
--     sorry

-- noncomputable def buchberger_algorithm_computable_finset
--   (gen: Finset (FiniteVarPoly σ R))
--   : Finset (FiniteVarPoly σ R) :=
--   let n := gen.card
--   if n ≤ 1 then
--     gen
--   else
--     buchberger_step_computable_finset gen []

-- end finset

-- -- This algorithm handles FiniteVarPoly, which has computable operation
-- section list

-- -- Generate new basis by checking (k, k+1), (k, k+2), ...
-- -- Get reduction result of Spoly (ith, (i + k + 1)th)
-- def find_new_basis_computable_list
--   (gen: List (FiniteVarPoly σ R))
--   (i k: ℕ) -- we will check i-th and (i + k + 1)-th from gen
--   : Option (FiniteVarPoly σ R) :=
--   let n := List.length gen
--   if k = 0 ∨ i ≥ n ∨ i + k + 1 ≥ n then
--     none
--   else
--     match List.drop i gen with
--     | [] => none
--     | _ :: [] => none
--     | gᵢ :: gen' =>
--       match List.drop k gen' with
--       | [] => none
--       | gₖ :: _ =>
--       let r := reduction_computable_list gen (Spoly_computable gᵢ gₖ)
--       if r = 0 then none else some r

-- -- 'gen' is basis set used to analyze s-polynomials, which size increases monotonically
-- -- new basis is added to head of basis set which changes index number of rest bases
-- -- initial argument are given with last two bases
-- -- total analysis ends when given pair is head of list and one-past the end of list
-- -- else, in the same situation except i is not in head of list, new pair with initial i is reduced one step is given
-- -- body of the algorithm first get reduced form of Spoly(i, i + k + 1)
-- -- if there's no addition of an basis, continue with increased k
-- -- else, do the same as other branch, but pointing index should updated
-- def buchberger_step_computable_list
--   (gen: List (FiniteVarPoly σ R))
--   (i k: ℕ)
--   : List (FiniteVarPoly σ R) :=
--   let n := List.length gen
--   if n ≤ 1 then
--     gen
--   else if i = 0 ∧ k ≥ (n - 1) then
--     gen
--   else if i + k + 2 > n then
--     buchberger_step_computable_list gen (i - 1) 0
--   else
--     let fp := find_new_basis_computable_list gen i 0
--     match fp with
--     | none => buchberger_step_computable_list gen i (k + 1)
--     | some p =>
--       buchberger_step_computable_list (p :: gen) (i + 1) (k + 1)
--   termination_by i
--   decreasing_by
--     all_goals simp_wf
--     · sorry
--     · sorry
--     · sorry

-- def buchberger_algorithm_computable_list
--   (gen: List (FiniteVarPoly σ R))
--   : List (FiniteVarPoly σ R) :=
--   let n := List.length gen
--   if n ≤ 1 then
--     gen
--   else
--     buchberger_step_computable_list gen (n - 0) 0

-- end list

-- end BuchbergerAlgorithm_computable
