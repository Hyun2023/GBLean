-- import GB.CFinsupp
import GB.Monomial
import GB.Polynomial
import GB.S_Poly
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division


section Reduction
-- variable
-- [DecidableEq (Monomial σ )]

-- Reduction Procedure, aka multivariate divison algorithm

noncomputable def Monomial.div [DecidableEq σ] (f : Monomial σ) (g : Monomial σ) : (Monomial σ) × (Monomial σ) :=
  if (Monomial.instDvd' f g)
  then (f / g, 0)
  else (0, f)

def Generators (σ R: Type) [DecidableEq σ] [CommRing R] : Type := Finset (MvPolynomial σ R)

instance Generators.instMembership (σ R: Type) [DecidableEq σ] [CommRing R] : Membership (MvPolynomial σ R) (Generators σ R) where
  mem := Finset.instMembership.mem

noncomputable def MvPolynomial.div [DecidableEq σ] [Field R] (f : MvPolynomial σ R) (g : MvPolynomial σ R) (g_ismon : is_monomial g) : (MvPolynomial σ R) × (MvPolynomial σ R) :=
  (f.divMonomial (g.toMonomial g_ismon), MvPolynomial.instSub.sub f (f.divMonomial (g.toMonomial g_ismon)))

lemma MvPolynomial.div_correct [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (f : MvPolynomial σ R) (g : MvPolynomial σ R) (g_ismon : is_monomial g):
  let (h,r) := f.div g g_ismon;
  f = g*h+r ∧
  (r = 0 ∨ ∀m ∈ monomials r, ¬ Monomial.instDvd.dvd (@leading_monomial σ _ _ _ ord g (is_monomial_nonzero g_ismon)) m) := sorry

-- Opaque
attribute [irreducible] MvPolynomial.div

noncomputable def MvPolynomial.multidiv_help [DecidableEq σ] [DecidableEq R] [LinearOrder σ] [Field R] (s : MvPolynomial σ R) (F : List (MvPolynomial σ R)) (F_isMonomial : ∀ f ∈ F, is_monomial f): (Finsupp (MvPolynomial σ R) (MvPolynomial σ R)) × (MvPolynomial σ R) :=
  match F with
  | [] => (0, s)
  | f :: F' =>
    let (h₁,r) := div s f (by simp at F_isMonomial; rcases F_isMonomial; assumption)
    let (h₂,r) := multidiv_help r F' (by intro f; simp at F_isMonomial; rcases F_isMonomial with ⟨_,h⟩ ; apply h)
    (h₂ + Finsupp.single f h₁, r)

lemma FList_isMonomial [CommRing R] {F : Finset (MvPolynomial σ R)} (F_isMonomial : ∀ f ∈ F, is_monomial f) : ∀ f ∈ F.toList, is_monomial f := by
  intro f fIn
  rw [Finset.mem_toList] at fIn
  apply F_isMonomial f fIn

noncomputable def MvPolynomial.multidiv [DecidableEq σ] [DecidableEq R] [LinearOrder σ]  [Field R] (s : MvPolynomial σ R) (F : Finset (MvPolynomial σ R)) (F_isMonomial : ∀ f ∈ F, is_monomial f) :
    (Finsupp (MvPolynomial σ R) (MvPolynomial σ R)) × (MvPolynomial σ R) :=
  MvPolynomial.multidiv_help s (F.toList) (FList_isMonomial F_isMonomial)

lemma Finset.sumEQ [CommRing R] (s: Finset (MvPolynomial σ R)) (f: (MvPolynomial σ R) -> (MvPolynomial σ R)): s.sum f = (s.toList.map f).sum := by
  unfold Finset.sum
  rw [← Multiset.sum_toList]
  have := Multiset.map_coe f s.toList
  simp at this; rw [this]; clear this; simp

lemma MvPolynomial.multidiv_correct [DecidableEq R] [LinearOrder σ] [ord : MonomialOrder σ] [Field R] (s : MvPolynomial σ R) (F : Finset (MvPolynomial σ R)) (F_isMonomial : ∀ f ∈ F, is_monomial f):
    -- let (a,r) := (MvPolynomial.multidiv s F F_isMonomial);
    s = (s.multidiv F F_isMonomial).snd + (∑ (f ∈ F), ((s.multidiv F F_isMonomial).fst f)*(f)) /\
    ((s.multidiv F F_isMonomial).snd = 0 ∨ ∀m ∈ monomials (s.multidiv F F_isMonomial).snd, ∀ f (inF : f ∈ F), ¬ Monomial.instDvd.dvd (leading_monomial f (is_monomial_nonzero (F_isMonomial f inF))) m) := by
  unfold multidiv; constructor
  . have : ∀ l (s : MvPolynomial σ R) F F_isMonomial (EQ: l = F.toList),
    s = (multidiv_help s l (by rw[EQ]; exact FList_isMonomial F_isMonomial)).2 + (∑ (f ∈ F), ((multidiv_help s l (by rw[EQ]; exact FList_isMonomial F_isMonomial)).1 f)*(f)) := by
      clear s F F_isMonomial
      intro l s F F_isMonomial EQ
      have F_isMonomial' := FList_isMonomial F_isMonomial
      rw [← EQ] at F_isMonomial'
      have EQ' : F = l.toFinset := by rw [EQ]; simp
      have G : ∀ l (s : MvPolynomial σ R) (l_isMonomial : ∀ f ∈ l, is_monomial f), s = (s.multidiv_help l l_isMonomial).2 + (l.map (fun f => (s.multidiv_help l l_isMonomial).1 f * f)).sum := by
        intro l; induction' l with f F' IH
        <;> intro s l_isMonomial
        . unfold multidiv_help; simp
        . simp [multidiv_help]
          have IH' := IH (div s f (by apply l_isMonomial; apply List.mem_cons_self)).2 (by intros; apply l_isMonomial; apply List.mem_cons_of_mem; assumption)
          have div_correct := (MvPolynomial.div_correct s f (by apply l_isMonomial; apply List.mem_cons_self)).1
          nth_rewrite 1 [div_correct]
          nth_rewrite 1 [IH']
          -- rw [IH']
          sorry
      nth_rewrite 1 [G l s F_isMonomial'];
      rw [Finset.sumEQ]; congr!
    apply this; rfl; assumption
  . sorry
