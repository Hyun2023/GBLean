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
import Mathlib.LinearAlgebra.Finsupp
-- import Mathlib.RingTheory.Ideal.Span


section Groebner

variable
[Finite σ]
[LinearOrder σ]
[DecidableEq σ]
[DecidableEq R]
[FieldR : Field R]
[ord : MonomialOrder σ]
-- [LinearOrder ( σ R)]

abbrev poly := MvPolynomial σ R

instance : Coe (Set (Monomial σ)) (Set (MvPolynomial σ R)) where
  coe := fun a => Set.image (fun m : Monomial σ  => ↑m) a

def leading_monomial_set (P : Set (MvPolynomial σ R))
  : Set (MvPolynomial σ R) :=
  let P_nonzero := {p ∈ P | p ≠ 0}
  let monomial_set := Set.image (leading_monomial_unsafe) (P_nonzero)
  monomial_set

def Groebner (G : Finset (MvPolynomial σ R))  (I : Ideal (MvPolynomial σ R)) :=
  Ideal.span G = I
  ∧
  Ideal.span (leading_monomial_set (Finset.toSet G))
  = Ideal.span (leading_monomial_set (I) )

-- def divisible (A B : Monomial σ) : Prop := True

lemma MonomialGen (m : MvPolynomial σ R) (mons : Finset (Monomial σ))
(m_mem : m ∈ Ideal.span ((fun a : (Monomial σ) => ↑a) '' mons)) :
  (is_monomial m) → ∃ mi : mons, ∃ k_poly : (MvPolynomial σ R), m = k_poly * mi :=
  by
    intro mon; have ismon := mon
    rw [is_monomial, ← MvPolynomial.finsupp_support_eq_support, Finsupp.card_support_eq_one] at mon
    rcases mon with ⟨a, ⟨ha1, ha2⟩⟩
    rw [Ideal.span, Finsupp.mem_span_iff_linearCombination] at m_mem; rcases m_mem with ⟨l, hm⟩
    have sup := Finsupp.mem_supported_support (MvPolynomial σ R) l
    rw [Finsupp.linearCombination_apply_of_mem_supported (MvPolynomial σ R) sup] at hm; simp; clear sup
    rw [Finset.sum_congr rfl] at hm
    any_goals intros x inx; rw [MvPolynomial.as_sum (l x)]

    case intro.intro.intro =>

    -- rw [MvPolynomial.single_eq_monomial] at ha2; rw [ha2] at hm
    have hl : ∀ i, i ∈ l.support → m.support = (l i • (↑i : MvPolynomial σ R)).support := by
    {
      intro i iin
      apply Finset.ext; intro am; constructor; intro amin
      {
      }
      rcases (IsTrichotomous.trichotomous m.support (l i • (↑i : MvPolynomial σ R)).support) with h | h
      { exact h }
      { sorry }
    }






-- def red (s : MvPolynomial σ R) (F : Finset (MvPolynomial σ R)) (F_nonzero : ∀ f ∈ F, f ≠ 0) :
--   (Finsupp (MvPolynomial σ R) (Monomial σ)) × (MvPolynomial σ R)   := sorry

def ReductionProp (s : MvPolynomial σ R) (G : Finset (MvPolynomial σ R)) (G_nonzero : ∀ g ∈ G, g ≠ 0)
(I : Ideal (MvPolynomial σ R))(r : MvPolynomial σ R) :=
  exists f,
  f ∈ I ∧
  s = r + f /\
    (r = 0 ∨ ∀m ∈ monomials r, ∀ g (inG : g ∈ G), ¬ Monomial.instDvd.dvd (leading_monomial g (G_nonzero g inG)) m)

def multidiv_Reduction (s : MvPolynomial σ R) (G : Finset (MvPolynomial σ R)) (G_nonzero : ∀ g ∈ G, g ≠ 0) :
  ReductionProp s G G_nonzero I (s.multidiv G G_nonzero).snd := by sorry

def Reduction_unique  (s : MvPolynomial σ R) (F : Finset (MvPolynomial σ R)) (GB : Groebner F I) (F_nonzero : ∀ f ∈ F, f ≠ 0)
  (H1 : (ReductionProp s F F_nonzero I r1) ) ( H2 : (ReductionProp s F F_nonzero I r2) ):
  r1 = r2 ∧ (s.multidiv F F_nonzero).snd  = r1 := by {
    constructor
    {
      by_cases r1=r2;assumption
      have ⟨ f1, ⟨ H11,H12 ⟩ ⟩ := H1
      have ⟨ f2, ⟨ H21,H22 ⟩ ⟩ := H2
    }
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
      have ⟨ _, H3⟩ := (Reduction_unique f G GB G_nonzero H H2)
      assumption
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

-- theorem BuchbergerCriterion :
--   forall (G : Finset (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) (G_nonzero : ∀ g ∈ G, g ≠ 0 ),
--     ( Groebner G I ) ↔ (∀ fi fj, fi ≠ fj → (red (S fi fj) G G_nonzero).2 = (0 : MvPolynomial σ R) ) := by
--     intros G I G_NZ
--     constructor
--     {
--       -- (==>)
--       intros GB fi fj neq
--       have ⟨ G_span, GB_prop ⟩ := GB
--       let (DD , Rem) := red (S fi fj) G sorry
--       have Sin: (S fi fj) ∈ I := by sorry
--       have RemIn: Rem ∈ I := by sorry
--       let DD_set := DD.frange
--       have h := @MonomialGen _ _ _ _ FieldR ord (leading_monomial Rem sorry)
--       have H := h DD_set
--     }
--     {
--       sorry
--     }

end Groebner
