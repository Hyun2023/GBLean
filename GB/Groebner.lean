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
-- import Mathlib.RingTheory.Ideal.Span

instance [CommRing R] : Coe (Set (Monomial σ)) (Set (MvPolynomial σ R)) where
  coe := fun a => Set.image (fun m => MvPolynomial.monomial m 1) a

def leading_monomial_set [Finite σ] [Field R] [MonomialOrder σ ] (P : Set (MvPolynomial σ R))
  : Set (MvPolynomial σ R) :=
  let P_nonzero := {p ∈ P | p ≠ 0}
  let monomial_set := Set.image (leading_monomial_unsafe) (P_nonzero)
  monomial_set

structure GroebnerBasis [Finite σ] [Field R] [MonomialOrder σ] (I : Ideal (MvPolynomial σ R))   where
  G : Finset (MvPolynomial σ R)
  G_spans_I : Ideal.span G = I
  -- leading_monomial : MvPolynomial σ R -> Monomial σ
  initial_spans_initial : Ideal.span (leading_monomial_set (Finset.toSet G))
  = Ideal.span (leading_monomial_set I)
