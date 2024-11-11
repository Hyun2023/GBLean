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

def Ideal.Lincomb [DecidableEq R] [CommRing R] (I : Ideal R) (S : Finset R)  (S_Span : Ideal.span S = I) :
  forall x, x ∈ I → ∃ (c : S → R), x = S.sum  (fun i : R => if sin : i ∈ S then c ⟨ i, sin⟩  else 0) := by
  sorry


section Groebner

variable
[Finite σ]
[DecidableEq σ]
[FieldR : Field R]
[ord : MonomialOrder σ ]
[LinearOrder (FiniteVarPoly σ R)]

abbrev Poly := FiniteVarPoly
abbrev Mon := Monomial

instance : Coe (Set (Monomial σ)) (Set (FiniteVarPoly σ R)) where
  coe := fun a => Set.image (fun m : Monomial σ  => ↑m) a

instance [CommRing R] : CommRing (FiniteVarPoly σ R) := sorry

def leading_monomial_unsafe' (p : FiniteVarPoly σ R) : (Monomial σ) :=
  sorry

def leading_monomial_set (P : Set (FiniteVarPoly σ R))
  : Set (FiniteVarPoly σ R) :=
  let P_nonzero := {p ∈ P | p ≠ 0}
  let monomial_set := Set.image (leading_monomial_unsafe') (P_nonzero)
  monomial_set

def Groebner (G : Finset (FiniteVarPoly σ R))  (I : Ideal (FiniteVarPoly σ R)) :=
  Ideal.span G = I
  ∧
  Ideal.span (leading_monomial_set (Finset.toSet G))
  = Ideal.span (leading_monomial_set (I) )

def divisible (A B : Mon σ) : Prop := True

instance MonomialSetCoercion2 : Coe (Finset (Monomial σ)) (Set (MvPolynomial σ R)) where
  coe := fun a => Set.image (fun m : Monomial σ  => Monomial.toMvPolynomial.coe m) a

structure term (σ R : Type) [CommRing R] :=
  mon : Monomial σ
  coeff : R

instance : Coe (term σ R) (FiniteVarPoly σ R) where
  coe := fun t => ↑(t.mon)

noncomputable instance : Coe (term σ R) (MvPolynomial σ R) where
  coe := fun t =>  ofFiniteVarPoly.coe ↑t

instance term_to_poly_set : Coe (Finset (term σ R)) (Set (MvPolynomial σ R)) where
  coe := fun a => Set.image (fun t : term σ R => ofFiniteVarPoly.coe ↑t) a

lemma MonomialGen (m : term σ R) (mons : Finset (term σ R)) (m_mem : ↑m ∈ Ideal.span (term_to_poly_set.coe mons)) :
  ∃ mi : mons, ∃ k_poly : (MvPolynomial σ R), m = k_poly * mi := by
  let p := fun m => ∃ mi : mons, ∃ k_poly : (MvPolynomial σ R), m = k_poly * mi
  have := @Submodule.span_induction R _ _ _ _ m p
  sorry


theorem BuchbergerCriterion :
  forall (G : Finset (FiniteVarPoly σ R))  (I : Ideal (FiniteVarPoly σ R)),
    ( Groebner G I ) ↔ (∀ fi fj, fi ≠ fj → red (S fi fj) G = 0) := by
    intros G I
    constructor
    {
      -- (==>)
      intros GB fi fj neq
      have ⟨ G_span, GB_prop ⟩ := GB
      let Rem := red (S fi fj) G
      have Sin: (S fi fj) ∈ I := by sorry
      have RemIn: Rem ∈ I := by sorry
      have : ∃ f :G , divisible (leading_monomial_unsafe' Rem) (@leading_monomial_unsafe' _ _ FieldR f) := by sorry
      have h := I.Lincomb G G_span Rem RemIn
      sorry
    }
    {
      sorry
    }

end Groebner
