-- TODO
-- 1. Define Groebner basis
-- 2. State and prove Buchberger Criterion
import Mathlib.Data.Finite.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Basic
import GB.Monomial
import GB.Polynomial
import GB.Reduction
import GB.S_Poly
-- import Mathlib.RingTheory.Ideal.Span

instance [DecidableEq σ] [Field R] : Coe (Set (Monomial σ)) (Set (FiniteVarPoly σ R)) where
  coe := fun a => Set.image (fun m : Monomial σ  => ↑m) a

instance [CommRing R] : CommRing (FiniteVarPoly σ R) := sorry

def leading_monomial_unsafe' [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : FiniteVarPoly σ R) : (Monomial σ) :=
  sorry

def leading_monomial_set [DecidableEq σ] [Finite σ] [Field R] [MonomialOrder σ ] (P : Set (FiniteVarPoly σ R))
  : Set (FiniteVarPoly σ R) :=
  let P_nonzero := {p ∈ P | p ≠ 0}
  let monomial_set := Set.image (leading_monomial_unsafe') (P_nonzero)
  monomial_set


structure GroebnerBasis [DecidableEq σ] [Finite σ] [Field R] [MonomialOrder σ] where
  G : Finset (FiniteVarPoly σ R)
  I : Ideal (FiniteVarPoly σ R)
  G_spans_I : Ideal.span G = I
  -- leading_monomial : MvPolynomial σ R -> Monomial σ
  initial_spans_initial : Ideal.span (leading_monomial_set (Finset.toSet G))
  = Ideal.span (leading_monomial_set I)

def isGB  [DecidableEq σ] [Finite σ] [Field R] [MonomialOrder σ]
(G : Finset (FiniteVarPoly σ R)) (I : Ideal (FiniteVarPoly σ R)) :=
  ∃(GB : GroebnerBasis) , GB.G = G /\ GB.I = I

theorem BuchbergerCriterion [DecidableEq σ] [Finite σ] [Field R] [MonomialOrder σ] :
  forall (I : Ideal (FiniteVarPoly σ R)) (G : Finset (FiniteVarPoly σ R)),
    (isGB G I) ↔ (∀ gi gj, gi ≠ gj → red (S gi gj) G = 0) := by
    sorry
