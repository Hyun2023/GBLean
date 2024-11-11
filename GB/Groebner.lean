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



lemma MonomialGen (m : MvPolynomial σ R) (mons : Finset (Monomial σ))
(m_mem : m ∈ Ideal.span ((fun a : (Monomial σ) => ↑a) '' mons)) :
   (is_monomial (toFiniteVarPoly.coe m)) → ∃ mi : mons, ∃ k_poly : (MvPolynomial σ R), m = k_poly * mi := by


  let p := fun m : (MvPolynomial σ R) => (is_monomial (toFiniteVarPoly.coe m)) → ∃ mi : mons, ∃ k_poly : (MvPolynomial σ R), m = k_poly * mi

  have : ((is_monomial (toFiniteVarPoly.coe m)) → ∃ mi : mons, ∃ k_poly : (MvPolynomial σ R), m = k_poly * mi)
  = p m := by rfl
  rw [this];clear this

  apply @Submodule.span_induction (MvPolynomial σ R) _ _ _ _ _
  {
    exact m_mem
  }
  {
    unfold p
    simp
    intros a ain ismon
    exists a; exists ain; exists 1;ring
  }
  {
    unfold p
    intro is_mon
    have H : ((@toFiniteVarPoly σ R).coe 0) = 0 := by {
      rfl
    }
    rw [H] at is_mon
    apply zero_is_not_mon at is_mon
    contradiction
  }
  {
    intros x y px py
    unfold p
    sorry
  }
  {
    sorry
  }


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
