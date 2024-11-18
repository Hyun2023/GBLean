-- Todo
-- 1. Define Buchberger algorithms in two version, one with FiniteVarPoly, and another just Mvpoly

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import GB.Monomial
import GB.Polynomial
import GB.Reduction
import GB.S_Poly
import GB.Groebner
open Monomial

-- Handles MvPolynomial, which operations are noncomputable
section BuchbergerAlgorithm

variable {σ: Type} {R: Type}
[DecidableEq σ]
[Finite σ]
[FR : Field R]
-- Field로부터 유도되는 성질
[IsNoetherianRing R]
[DecidableEq R]
[LinearOrder σ]
[ord : MonomialOrder σ ]



def Spoly (f g : MvPolynomial σ R) : MvPolynomial σ R := sorry

def s_red [MonomialOrder σ] (p q : MvPolynomial σ R) (F : Finset (MvPolynomial σ R)) (F_nonzero : ∀ f ∈ F, f ≠ 0): MvPolynomial σ R :=
  ((S p q).multidiv F F_nonzero).snd

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

def buchberger_step_monotone
  (pair_list :  List (MvPolynomial σ R × MvPolynomial σ R))
  (G_queue : Finset (MvPolynomial σ R))
  (G' : Finset (MvPolynomial σ R)) (G'_nonzero : ∀ g ∈ G', g ≠ 0)
  :  G_queue ⊆ (buchberger_step pair_list G_queue G' G'_nonzero) := by sorry


def buchberger_step_keep_nonzero
  (G: Finset (MvPolynomial σ R))
  (G_queue : Finset (MvPolynomial σ R))
  (G_nonzero : ∀ g ∈ G, g ≠ 0)
  (G_queue_nonzero : ∀ g ∈ G_queue, g ≠ 0  ) :
  ∀ g ∈ (buchberger_step (G.product G).toList G_queue G (G_nonzero)), g ≠ 0 := by
  induction (G.product G).toList generalizing G_queue with
  |nil => sorry
  |cons hd tl ih => sorry

def buchberger_step_keep_nonempty
  (G: Finset (MvPolynomial σ R))
  (G_nonzero : ∀ g ∈ G, g ≠ 0)
  (G_queue_nonzero : ∀ g ∈ G_queue, g ≠ 0  )
  (G_nonempty: Nonempty G):
  Nonempty (buchberger_step (G.product G).toList G_queue G (G_nonzero)) := by
  sorry

def buchberger_step_keep_membership
  (F G: Finset (MvPolynomial σ R))
  (G_nonzero : ∀ g ∈ G, g ≠ 0)
  (Gmember : G_queue.toSet ⊆ SetLike.coe (Ideal.span F) ) :
  (buchberger_step (G.product G).toList G_queue G (G_nonzero)).toSet ⊆ SetLike.coe (Ideal.span F) := by

  induction (G.product G).toList generalizing G_queue with
  |nil => unfold buchberger_step;assumption
  |cons hd tl ih => {
    have (p,q) := hd
    by_cases pqeq : p=q
    {
      unfold buchberger_step;simp [pqeq]
      apply ih;assumption
    }
    {
      unfold buchberger_step;simp [pqeq]
      by_cases red0 : s_red p q G G_nonzero = 0
      {
        simp [red0];apply ih;assumption
      }
      {
        simp [red0];apply ih
        sorry
      }
    }
  }


-- def ideal_order_wf : WellFounded (@ideal_order σ R _ _ _ ord) := sorry

instance wf : WellFoundedRelation (Ideal (MvPolynomial σ R)) where
  rel := fun x y => x>y
  wf := by {
    apply IsNoetherian.wf; apply MvPolynomial.isNoetherianRing
  }

noncomputable def buchberger_algorithm
  (G : Finset (MvPolynomial σ R))
  (G_nonzero : ∀ g ∈ G, g ≠ 0)
  (G_nonempty : Nonempty G)
  : Finset (MvPolynomial σ R) :=
  let G' := buchberger_step (G.product G).toList G G (G_nonzero)
  if h : G' = G then
    G
  else
    buchberger_algorithm G' (by { apply buchberger_step_keep_nonzero G;assumption }) (
      by { apply buchberger_step_keep_nonempty; all_goals assumption}
    )
  termination_by (Ideal.span (toMvPolynomial_Finset (@leading_monomial_finset σ R _ _ ord G)).toSet : Ideal (MvPolynomial σ R))
  decreasing_by {
    -- Look at the page 90 Theorem 2
    sorry
  }

def buchberger_fixpoint
(G : Finset (MvPolynomial σ R))
  (G_nonzero : ∀ g ∈ G, g ≠ 0)
  (G_nonempty : Nonempty G) :
  let GB := buchberger_algorithm G G_nonzero G_nonempty
  buchberger_step (GB.product GB).toList GB GB sorry = GB := by sorry

def buchberger_correct
(G : Finset (MvPolynomial σ R))
  (G_nonzero : ∀ g ∈ G, g ≠ 0)
  (G_nonempty : Nonempty G) :
  let GB := buchberger_algorithm G G_nonzero G_nonempty
  Groebner GB (Ideal.span G) := by {
    intros GB
    have GB_def : GB = buchberger_algorithm G G_nonzero G_nonempty := by rfl
    have GB_nonzero : ∀g ∈ GB, g ≠ 0 := by sorry
    have GB_nonempty : Nonempty GB := by sorry
    rw [BuchbergerCriterion (G_nonzero := GB_nonzero)]
    have H := buchberger_fixpoint G G_nonzero G_nonempty
    simp at H
    have GB_fix := H
    contrapose! H
    rw [<-GB_def]
    unfold buchberger_step

    have ⟨ p, q, pin, qin, pneq , S_zero⟩ := H

    induction ((GB.product GB).toList) with
    |nil =>{
      -- GB가 Nonempty인데 모순
      sorry
    }
    |cons hd tl ih =>{
      -- (hd = (p,q) 이거나 tl에 (p,q)가 있음)
      have pqH : hd = (p,q) ∨ (p,q) ∈ tl := by sorry
      cases pqH with
      |inl pq => {
        unfold s_red
        simp [pq,pneq,S_zero];
        intros H
        have monotone := buchberger_step_monotone tl (GB ∪ {s_red p q GB GB_nonzero}) GB GB_nonzero
        unfold s_red at monotone
        rw [H] at monotone
        by_cases Sin : ((S p q).multidiv GB GB_nonzero).2 ∈ GB
        {
          have : (GB ∪ {((S p q).multidiv GB GB_nonzero).2}) = GB := by {
          simp [<- Finset.insert_eq];assumption
          }
          rw [this] at H;unfold buchberger_step at H; contradiction
        }
        {
          -- Because S is not in GB, GB ∪ S is larger than GB, which is contradict to monotone
          sorry
        }
      }
      |inr pq => {
          have (p',q') := hd;simp
          by_cases pqeq' : p' = q'
          · simp [pqeq'];unfold buchberger_step;assumption
          simp [pqeq']
          by_cases name : s_red p' q' GB GB_nonzero = 0
          · simp [name];unfold buchberger_step;assumption
          simp [name]
          -- 위와 같은 증명, buchberger_step에서 G_queue 위치에 있는게 작아질수는 없다는걸 증명하면 됨
          sorry
      }
    }
  }






end finset

-- This algorithm handles FiniteVarPoly, which has computable operation
-- section list

-- -- Generate new basis by checking (k, k+1), (k, k+2), ...
-- -- Get reduction result of Spoly (ith, (i + k + 1)th)
-- noncomputable def find_new_basis_list
--   (gen: List (MvPolynomial σ R))
--   (i k: ℕ) -- we will check i-th and (i + k + 1)-th from gen
--   : Option (MvPolynomial σ R) :=
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
--       let r := reduction_list gen (Spoly gᵢ gₖ)
--       if r = 0 then none else some r



-- -- 'gen' is basis set used to analyze s-polynomials, which size increases monotonically
-- -- new basis is added to head of basis set which changes index number of rest bases
-- -- initial argument are given with last two bases
-- -- total analysis ends when given pair is head of list and one-past the end of list
-- -- else, in the same situation except i is not in head of list, new pair with initial i is reduced one step is given
-- -- body of the algorithm first get reduced form of Spoly(i, i + k + 1)
-- -- if there's no addition of an basis, continue with increased k
-- -- else, do the same as other branch, but pointing index should updated
-- noncomputable def buchberger_step_list
--   (G: List (MvPolynomial σ R))
--   (i k: ℕ)
--   : List (MvPolynomial σ R) :=
--   let n := G.length
--   if G.length ≤ 1 then
--     G
--   else if i = 0 ∧ k ≥ (n - 1) then
--     gen
--   else if i + k + 2 > n then
--     buchberger_step_list gen (i - 1) 0
--   else
--     let fp := find_new_basis_list gen i 0
--     match fp with
--     | none => buchberger_step_list gen i (k + 1)
--     | some p =>
--       buchberger_step_list (p :: gen) (i + 1) (k + 1)
--   termination_by i
--   decreasing_by
--     all_goals simp_wf
--     · sorry
--     · sorry
--     · sorry

-- noncomputable def buchberger_algorithm_list
--   (F: List (MvPolynomial σ R))
--   : List (MvPolynomial σ R) :=
--   -- let n := F.length

--   if F.length <=1 then
--     F
--   else
--     buchberger_step_list F (n - 0) 0

-- end list

-- end BuchbergerAlgorithm



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
