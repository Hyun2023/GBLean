-- TODO
-- 1. Define Groebner basis
-- 2. State and prove Buchberger Criterion
import Mathlib.Data.Finite.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Multiset.Basic
import GB.Monomial
import GB.Polynomial
import GB.Reduction
import GB.S_Poly
-- import GB.CFinsupp
-- import Mathlib.LinearAlgebra.Finsupp
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.BigOperators


section Groebner
open MvPolynomial
variable
[Finite σ]
[LinearOrder σ]
[DecidableEq σ]
[DecidableEq R]
[FieldR : Field R]
[ord : MonomialOrder σ ]
-- [LinearOrder ( σ R)]

abbrev poly := MvPolynomial σ R

instance : Coe (Set (Monomial σ)) (Set (MvPolynomial σ R)) where
  coe := fun a => Set.image (fun m : Monomial σ  => ↑m) a

def toMvPolynomial_Set (M : Set (Monomial σ)) :
  Set (MvPolynomial σ R) :=
  M.image (fun m : Monomial σ  => ↑m)

noncomputable def toMvPolynomial_Finset (M : Finset (Monomial σ)) :
  Finset (MvPolynomial σ R) :=
  M.image (fun m : Monomial σ  => ↑m)



def leading_monomial_set (P : Set (MvPolynomial σ R))
  : Set (Monomial σ) :=
  { m | ∃ (p : MvPolynomial σ R) (h : p ≠ 0), p ∈ P ∧ m = leading_monomial p h }

noncomputable def leading_monomial_finset (P : Finset (MvPolynomial σ R))
  : Finset (Monomial σ) :=
  let P_underlying := P.val
  let P_filtered := P_underlying.filterMap (fun p => (leading_monomial_option p).map (fun o => ↑o))
  P_filtered.toFinset


axiom leading_monomial_unwrap (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) :
  leading_monomial_unsafe p = leading_monomial p p_nonzero

def Groebner (G : Finset (MvPolynomial σ R))  (I : Ideal (MvPolynomial σ R)) :=
  Ideal.span G = I
  ∧
  Ideal.span (toMvPolynomial_Finset (leading_monomial_finset G )).toSet
  = Ideal.span (@toMvPolynomial_Set _ R _ (@leading_monomial_set _ R _ _ ord (I) ))

lemma MonomialGen (m : MvPolynomial σ R) (mons : Finset (Monomial σ))
(m_mem : m ∈ Ideal.span ((fun a : (Monomial σ) => ↑a) '' mons)) :
  (h : is_monomial m) → ∃ mi, mi ∈  mons ∧ ( mi ∣ m.toMonomial h ) := by sorry

-- def red (s : MvPolynomial σ R) (F : Finset (MvPolynomial σ R)) (F_nonzero : ∀ f ∈ F, f ≠ 0) :
--   (Finsupp (MvPolynomial σ R) (Monomial σ)) × (MvPolynomial σ R)   := sorry

def ReductionProp (s : MvPolynomial σ R) (G : Finset (MvPolynomial σ R)) (G_nonzero : ∀ g ∈ G, g ≠ 0)
(I : Ideal (MvPolynomial σ R)) (r : MvPolynomial σ R) :=
  exists f,
  f ∈ I ∧
  s = r + f /\
    (r = 0 ∨ ∀m ∈ monomials r, ∀ g (inG : g ∈ G), ¬ Monomial.instDvd.dvd (leading_monomial g (G_nonzero g inG)) m)

def multidiv_reduction (s : MvPolynomial σ R) (G : Finset (MvPolynomial σ R)) (G_nonzero : ∀ g ∈ G, g ≠ 0)
  (I : Ideal (MvPolynomial σ R)) :
  ReductionProp s G G_nonzero I (s.multidiv G G_nonzero).snd := by sorry

def Reduction_unique  (s : MvPolynomial σ R) (G : Finset (MvPolynomial σ R)) (GB : Groebner G I) (G_nonzero : ∀ g ∈ G, g ≠ 0)
  (H1 : (ReductionProp s G G_nonzero I r1) ) ( H2 : (ReductionProp s G G_nonzero I r2) ):
  r1 = r2 := by {
    have ⟨G_span , GB⟩ := GB
    by_cases eq: r1=r2;assumption
    have ⟨ f1, ⟨ H11,H12,H13 ⟩ ⟩ := H1
    have ⟨ f2, ⟨ H21,H22,H23 ⟩ ⟩ := H2

    have sub_in : r1 - r2 ∈ I := by sorry
    have sub_nonzero : r1 -r2 ≠ 0 := by {
      contrapose!;intros;exact sub_ne_zero_of_ne eq
    }
    have lm_in : ( @toMvPolynomial R _ _ (leading_monomial (r1 -r2) sub_nonzero) ∈ Ideal.span (toMvPolynomial_Finset (leading_monomial_finset G )).toSet ) := by {
      rw [GB];apply Ideal.subset_span
      unfold leading_monomial_set;simp
      unfold toMvPolynomial_Set;simp
      exists (leading_monomial (r1 -r2) sub_nonzero);constructor
      exists (r1 -r2);constructor;assumption
      exists sub_nonzero;rfl
    }

    have lm_in' : ( @toMvPolynomial R _ _ (leading_monomial (r1 -r2) sub_nonzero) ) ∈
      Ideal.span ((fun a ↦ (monomial a) 1) '' (leading_monomial_finset G).toSet) := by sorry
    have ⟨ mi, ⟨ mi_in, mi_dvd⟩  ⟩  := @MonomialGen _ R _ _ _ _ _ _
      (toMvPolynomial (leading_monomial (r1 - r2) sub_nonzero))
      (leading_monomial_finset G) lm_in' (mono_poly_mono _)

  -- Now we prove that r1-r2 is divided by some lm(gi). But it's cannot be true because
  -- no term of r1 is divided by any g except r is 0. Complete proof is left as excercise :)
    sorry
}

def S (f g : MvPolynomial σ R) : MvPolynomial σ R := sorry

lemma GB_multidiv (G : Finset (MvPolynomial σ R))  (G_nonzero : ∀ g ∈ G, g ≠ 0) (I : Ideal (MvPolynomial σ R)) (f  : MvPolynomial σ R) :
  Groebner G I -> (
    f ∈ I ↔ (f.multidiv G G_nonzero).snd = 0
  ) := by
    intros GB
    have ⟨G_span , _⟩ := GB
    constructor
    {
      intros
      have H : ReductionProp f G G_nonzero I 0 := by {
        unfold ReductionProp;exists f;constructor;assumption
        constructor;simp
        left;simp
      }
      have H2 : ReductionProp f G G_nonzero I (f.multidiv G G_nonzero).snd := by{
        unfold ReductionProp
        exists (∑ (g ∈ G), ((f.multidiv G G_nonzero).fst g)*(g))
        constructor
        · apply Ideal.sum_mem;intros c cin
          apply Ideal.mul_mem_left
          rw [<-G_span]
          apply Ideal.subset_span;assumption
        · apply (f.multidiv_correct G G_nonzero)
      }
      have H3 := (Reduction_unique f G GB G_nonzero H H2)
      exact id (Eq.symm H3)
    }
    {
      intros r_prop
      have ⟨H,_⟩ := f.multidiv_correct G G_nonzero
      rw [H, <- G_span, r_prop]
      simp
      apply Ideal.sum_mem
      intros c cin
      apply Ideal.mul_mem_left
      apply Ideal.subset_span;assumption
    }

theorem BuchbergerCriterion :
  forall (G : Finset (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) (G_nonzero : ∀ g ∈ G, g ≠ 0 ),
    ( Groebner G I ) ↔ (∀ fi fj, fi∈ G -> fj ∈ G -> fi ≠ fj → ((S fi fj).multidiv G G_nonzero).2 = 0 ) := by
    intros G I G_NZ
    constructor
    {
      -- (==>)
      intros GB fi fj neq
      have Sin: (S fi fj) ∈ I := by sorry
      intros
      exact (GB_multidiv G G_NZ I (S fi fj) GB).mp Sin
    }
    {
      -- (<==)
      intros cond
      sorry
    }

end Groebner
