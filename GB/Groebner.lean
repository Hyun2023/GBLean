-- TODO
-- 1. Define Groebner basis
-- 2. State and prove Buchberger Criterion
import Mathlib.Data.Finite.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.RingTheory.Ideal.Basic
import GB.Monomial
import GB.Polynomial
import GB.Reduction
import GB.S_Poly
import GB.CFinsupp
-- import Mathlib.RingTheory.Ideal.Span

def Ideal.Lincomb [DecidableEq R] [CommRing R] (I : Ideal R) (S : Finset R)  (S_Span : Ideal.span S = I) :
  forall x, x ∈ I → ∃ (c : S → R), x = S.sum  (fun i : R => if sin : i ∈ S then c ⟨ i, sin⟩  else 0) := by
  sorry


section Groebner

variable
[Finite σ]
[DecidableEq σ]
[FieldR : Field R]
[ord : MonomialOrder σ ]
-- [LinearOrder ( σ R)]

instance : Coe (Set (Monomial σ)) (Set (MvPolynomial σ R)) where
  coe := fun a => Set.image (fun m : Monomial σ  => ↑m) a

instance [CommRing R] : CommRing (MvPolynomial σ R) := sorry

def leading_monomial_unsafe' (p : MvPolynomial σ R) : (Monomial σ) :=
  sorry

def leading_monomial_set (P : Set (MvPolynomial σ R))
  : Set (MvPolynomial σ R) :=
  let P_nonzero := {p ∈ P | p ≠ 0}
  let monomial_set := Set.image (leading_monomial_unsafe') (P_nonzero)
  monomial_set

def Groebner (G : Finset (MvPolynomial σ R))  (I : Ideal (MvPolynomial σ R)) :=
  Ideal.span G = I
  ∧
  Ideal.span (leading_monomial_set (Finset.toSet G))
  = Ideal.span (leading_monomial_set (I) )

-- def divisible (A B : Monomial σ) : Prop := True

-- lemma MonomialGen (m : MvPolynomial σ R) (mons : Finset (Monomial σ))
-- (m_mem : m ∈ Ideal.span ((fun a : (Monomial σ) => ↑a) '' mons)) :
--    (is_monomial (toFiniteVarPoly.coe m)) → ∃ mi : mons, ∃ k_poly : (MvPolynomial σ R), m = k_poly * mi := by sorry


-- theorem BuchbergerCriterion :
--   forall (G : Finset (FiniteVarPoly σ R))  (I : Ideal (FiniteVarPoly σ R)),
--     ( Groebner G I ) ↔ (∀ fi fj, fi ≠ fj → red (S fi fj) G = 0) := by
--     intros G I
--     constructor
--     {
--       -- (==>)
--       intros GB fi fj neq
--       have ⟨ G_span, GB_prop ⟩ := GB
--       let Rem := red (S fi fj) G
--       have Sin: (S fi fj) ∈ I := by sorry
--       have RemIn: Rem ∈ I := by sorry
--       have : ∃ f :G , divisible (leading_monomial_unsafe' Rem) (@leading_monomial_unsafe' _ _ FieldR f) := by sorry
--       have h := I.Lincomb G G_span Rem RemIn
--       sorry
--     }
--     {
--       sorry
--     }

end Groebner
