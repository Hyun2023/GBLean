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

structure GroebnerBasis (σ R : Type) [Finite σ] [fr: Field R] [MonomialOrder σ]  where
  G : Finset (MvPolynomial σ R)
  I : Ideal (MvPolynomial σ R)
  G_spans_I : Ideal.span G = I
  leading_monomial : MvPolynomial σ R -> Monomial σ
  initial_spans_initial : Ideal.span (Set.image (fun m => MvPolynomial.monomial m 1) (Set.image leading_monomial (Finset.toSet G)))
  = Ideal.span (Set.image (fun m => MvPolynomial.monomial m 1) (Set.image leading_monomial I))
