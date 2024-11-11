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

instance term_to_FiniteVarPoly : Coe (term σ R) (FiniteVarPoly σ R) where
  coe := fun t => ↑(t.mon)

noncomputable instance term_to_MvPolynomial : Coe (term σ R) (MvPolynomial σ R) where
  coe := fun t =>  ofFiniteVarPoly.coe ↑t

instance term_to_poly_set : Coe (Finset (term σ R)) (Set (MvPolynomial σ R)) where
  coe := fun a => Set.image (fun t : term σ R => ofFiniteVarPoly.coe ↑t) a

lemma MonomialGen (m : term σ R) (mons : Finset (term σ R)) (m_mem : ↑m ∈ Ideal.span (term_to_poly_set.coe mons)) :
  ∃ mi : mons, ∃ k_poly : (MvPolynomial σ R), m = k_poly * mi := by
  let p := fun m => ∃ mi : mons, ∃ k_poly : (MvPolynomial σ R), m = k_poly * mi
  have : (∃ mi : mons, ∃ k_poly : (MvPolynomial σ R), m = k_poly * mi) = p m := by rfl
  rw [this];clear this
  apply @Submodule.span_induction (MvPolynomial σ R) _ _ _ _ _ mons
  {
    exact m_mem
  }
  {
    simp
    intros a ain
    unfold p
    exists ⟨a,ain⟩;exists 1
    ring
  }
  {
    unfold p
    -- mons에 nonempty조건이 필요한지? nonempty면 거기서 choose해서 넣고 k_poly 0으로 주면 됨
    sorry
  }
  {
    intros x y px py
    have ⟨mx,kx,mx_prop⟩ := px
    have ⟨my,ky,my_prop⟩ := px
    unfold p
    -- px 랑 py 부수면 각각 mi랑 k_poly 나옴. mx=my면 kx+ky 주면 되고 아니라면 어카더라요?
  }
  {
    intros a x px
    have ⟨m,k,m_prop⟩ := px
    unfold p
    exists m;exists a • k
    simp [m_prop];ring
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
