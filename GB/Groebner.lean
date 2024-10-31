-- TODO
-- 1. Define Groebner basis
-- 2. State and prove Buchberger Criterion
import Mathlib.Data.Finite.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.RingTheory.Ideal.Basic
-- import Mathlib.RingTheory.Ideal.Span

structure GroebnerBasis (σ R : Type) [Finite σ] [fr: Field R]  where
  G : Finset (MvPolynomial σ R)
  I : Ideal (MvPolynomial σ R)
