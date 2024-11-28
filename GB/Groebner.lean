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
[ord : MonomialOrder σ]
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
  (is_monomial m) → ∃ mi : mons, ∃ k_poly : (MvPolynomial σ R), m = k_poly * mi :=
  by
    intro mon; have ismon := mon
    rw [is_monomial] at mon
    rcases mon with ⟨⟨mon, ⟨⟨min, _⟩, munique⟩⟩, _⟩
    simp at munique
    rw [Ideal.span, Finsupp.mem_span_iff_linearCombination] at m_mem
    rcases m_mem with ⟨l, hm⟩
    rw [Finsupp.linearCombination_apply (MvPolynomial σ R)] at hm; simp
    rw [Finsupp.sum] at hm
    rw [Finset.sum_congr rfl] at hm

    any_goals intro x xin; rw [MvPolynomial.as_sum (l x)]

    rw [← SMul.smul_eq_hSMul] at hm
    have comm :
      ∀ x ∈ l.support, (∑ v ∈ (l x).support, (monomial v) (coeff v (l x))) • ↑x
      = (∑ v ∈ (l x).support, (monomial v) (coeff v (l x)) • (x : MvPolynomial σ R)) := by {
        intros x xin
        rw [Finset.sum_smul]
      }
    rw [Finset.sum_congr rfl] at hm
    any_goals apply comm
    clear comm
    rw [Finset.sum_sigma'] at hm

    have test :
      ∃ x ∈ l.support.sigma fun x ↦ (l x).support,
        ((monomial x.snd) (1 : R)) • (x.fst : MvPolynomial σ R) = monomial mon 1 := by {
          apply of_not_not; intros neg
          rw [← hm] at min
          apply Finsupp.mem_support_finset_sum at min
          rcases min with ⟨c, min1, min2⟩
          apply neg; exists c; constructor
          { exact min1 }
          rcases c with ⟨c1, c2⟩; simp at min2
          simp
          have exi : ∃ mono ∈ mons, monomial mono 1 = c1.val := by {
            rcases c1 with ⟨c1, c1in⟩; rw [Set.mem_image] at c1in
            rcases c1in with ⟨c1m, c1min⟩
            exists c1m
          }
          rcases exi with ⟨mono, hmono, hmono2⟩
          rw [← hmono2]; simp
          rw [← hmono2] at min2; simp at min2
          rw [← MvPolynomial.single_eq_monomial, Finsupp.single_apply] at min2
          split_ifs at min2; any_goals trivial
        }
    rcases test with ⟨⟨xf, xs⟩, hx, hx2⟩
    simp at hx2

    rcases xf with ⟨xf, xfin⟩
    rw [Set.mem_image] at xfin; rcases xfin with ⟨xfm, xfmin1, xfmin2⟩

    exists xfm; constructor
    { rw [← mons.mem_coe]; exact xfmin1 }
    rw [xfmin2]
    have meq :
      m = (monomial mon) (m.coeff mon) := by {
        apply m.ext; intros m_1; simp
        split_ifs with neq_m_m1
        rw [neq_m_m1]
        specialize (munique m_1)
        contrapose! munique
        constructor; trivial
        symm; trivial
      }
    rw [meq]
    exists (monomial xs (coeff mon m))
    simp at hx2
    have meq : (monomial xs) (coeff mon m) = (MvPolynomial.C (coeff mon m)) * (monomial xs 1) := by
    {
      ext n; simp
    }
    rw [meq, mul_assoc, hx2]
    rw [MvPolynomial.C_mul_monomial]; simp


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
        -- · apply (f.multidiv_correct G G_nonzero)
        · sorry
      }
      have H3 := (Reduction_unique f G GB G_nonzero H H2)
      exact id (Eq.symm H3)
    }
    {
      intros r_prop
      sorry
      -- have ⟨H, _⟩ := f.multidiv_correct G G_nonzero
      -- rw [H, <- G_span, r_prop]
      -- simp
      -- apply Ideal.sum_mem
      -- intros c cin
      -- apply Ideal.mul_mem_left
      -- apply Ideal.subset_span;assumption
    }

noncomputable def linearcomb_measure (G : Finset (MvPolynomial σ R)) (l : ↑↑G →₀ MvPolynomial σ R) : Monomial σ
  := @Finset.max' _ ord.toLinearOrder (Finset.image (fun x => leading_monomial ((Subtype.val x) * l x) sorry) (l.support)) sorry

instance wf : WellFoundedRelation (Monomial σ) where
  rel := fun x y => x < y
  wf := by {
    cases ord.isWellOrder with
    | @mk A B C =>
      cases C with
      | @mk WF => trivial
  }

theorem BuchbergerCriterion :
  forall (G : Finset (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R))
  (G_basis : Ideal.span G = I)
  (G_nonzero : ∀ g ∈ G, g ≠ 0 ),
    ( Groebner G I ) ↔ (∀ fi fj, fi∈ G -> fj ∈ G -> fi ≠ fj → ((S fi fj).multidiv G G_nonzero).2 = 0 ) := by
    intros G I G_basis G_nonzero
    constructor
    {
      -- (==>)
      intros GB fi fj neq
      have Sin: (S fi fj) ∈ I := by sorry
      intros
      exact (GB_multidiv G G_nonzero I (S fi fj) GB).mp Sin
    }
    {
      -- (<==)
      intros cond
      unfold Groebner
      constructor; trivial
      apply le_antisymm
      · apply Ideal.span_mono
        /-
        prove
        ↑(toMvPolynomial_Finset (leading_monomial_finset G)) ⊆ toMvPolynomial_Set (leading_monomial_set ↑I)
        -/
        sorry
      · rw [Ideal.span_le]
        intros x L
        unfold toMvPolynomial_Set at L
        rw [Set.mem_image] at L
        obtain ⟨x_1, L, L'⟩ := L
        rw [← L']; clear L'
        unfold leading_monomial_set at L
        rw [Set.mem_setOf_eq] at L
        obtain ⟨p, p_nonzero, L, L'⟩ := L
        rw [L']; clear L'
        rw [← G_basis] at L
        rw [SetLike.mem_coe] at L
        rw [SetLike.mem_coe]
        rw [Ideal.span, Finsupp.mem_span_iff_linearCombination] at L
        obtain ⟨l, comb⟩ := L
        rw [Finsupp.linearCombination_apply (MvPolynomial σ R)] at comb
        clear x x_1
        generalize H : linearcomb_measure G l = measure
        revert p H l
        apply (@WellFounded.induction _ ((wf).rel) ((wf).wf) _ measure)
        intros measure IH p p_nonzero l l_sum l_measure
        rw [← (Finsupp.sum_filter_add_sum_filter_not (fun x => leading_monomial (l x * x.val) sorry = measure))] at l_sum
        have l_filter := Finsupp.support_filter (fun x ↦ leading_monomial (l x * x.val) sorry = measure) l
        generalize h : (Finsupp.filter (fun x ↦ leading_monomial (l x * x.val) sorry = measure) l) = l' at l_sum l_filter
        clear h
        let l'' := Finsupp.onFinset l'.support (fun x => (monomial (leading_monomial (l x * x.val) sorry)) (leading_coeff (l x * x.val) sorry)) sorry
        have E : l' = l'' + (l' - l'') := by sorry
        rw [E] at l_sum
        rw [Finsupp.sum_add_index] at l_sum
        · nth_rewrite 1 [Finsupp.sum] at l_sum
          generalize EE : ∑ a ∈ l''.support, l'' a • a.val = I

          sorry
        · sorry
        · sorry
        --rw [← (Finsupp.sum_filter_add_sum_filter_not (fun x => leading_monomial (lx * ↑x) = measure))] at l_sum
        -- unfold Finsupp.sum at comb; simp at comb
-- Finsupp.sum_filter_add_sum_filter_not
-- Finsupp.support_add_eq
-- Finset.sum_disjUnion
-- Finset.sum_union_inter
-- Finset.sum_union
        -- rw [Finset.sum_congr rfl] at comb
        -- any_goals intro x xin; rw [MvPolynomial.as_sum (l x)]
    }

end Groebner
