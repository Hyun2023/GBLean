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
  (f.divMonomial (g.toMonomial g_ismon), f.modMonomial (g.toMonomial g_ismon))

def MvPolynomial.monomial_equiv [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (g : MvPolynomial σ R) (g_ismon : is_monomial g) : g = (monomial (g.toMonomial g_ismon)) 1 := by
  rw [toMonomial]
  ext m
  rw [coeff, coeff]
  rw [monomial, AddMonoidAlgebra.lsingle]
  rw [Finsupp.lsingle]; simp
  have ⟨m0, ⟨m0P1, m0P2⟩⟩ := g_ismon
  simp at m0P1
  rw [DFunLike.coe, DFunLike.coe, Finsupp.instFunLike, LinearMap.instFunLike]; simp
  rw [LinearMap.instFunLike]; simp
  have EQ4 : (Finset.choose (fun x ↦ True) g.support g_ismon = m0) := by
    have EQ5 := (@Finset.choose_mem _ (fun _ ↦ True) _ g.support g_ismon)
    apply m0P2
    exact Finset.choose_spec (fun x ↦ True) g.support g_ismon
  rw [EQ4]
  rcases em (m ∈ g.support) with p | p
  . have EQ6 : m = m0 := by
      apply m0P2
      exact And.symm ⟨trivial, p⟩
    rw [<-EQ6]
    have EQ7 := (@Finsupp.single_eq_same _ _ _ m (@OfNat.ofNat R 1 One.toOfNat1))
    have EQ8 : g.toFun m = 1 := by
      sorry
    rw [EQ8]
    symm
    exact EQ7
  . have EQ6 : g m = 0 := by
      have EQ7 := (Finsupp.mem_support_toFun g m)
      have EQ8 : ¬ (g m ≠ 0) := by
        intro H
        apply p
        exact mem_support_iff.mpr H
      exact Function.nmem_support.mp EQ8
    have NEQ : m0 ≠ m := by
      intro H
      apply m0P1
      rw [coeff]
      rw [H]
      exact EQ6
    have EQ7 := (@Finsupp.single_eq_of_ne _ _ _ m0 m (@OfNat.ofNat R 1 One.toOfNat1) NEQ)
    have EQ8 : g.toFun m = 0 := by
      exact EQ6
    rw [EQ8]
    exact id (Eq.symm EQ7)

lemma MvPolynomial.div_correct [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (f : MvPolynomial σ R) (g : MvPolynomial σ R) (g_ismon : is_monomial g):
  let (h,r) := MvPolynomial.div f g g_ismon;
  f = g*h+r ∧
  (r = 0 ∨ ∀m ∈ monomials r, ¬ Monomial.instDvd.dvd (@leading_monomial σ _ _ _ ord g (is_monomial_nonzero g_ismon)) m) := by
  constructor
  . have EQ := (MvPolynomial.divMonomial_add_modMonomial f (g.toMonomial g_ismon))
    have EQ2 : (g * f.divMonomial (g.toMonomial g_ismon) = (monomial (g.toMonomial g_ismon)) 1 * f.divMonomial (g.toMonomial g_ismon)) := by
      have EQ3 : g = (monomial (g.toMonomial g_ismon)) 1 := by
        apply monomial_equiv
      exact congrFun (congrArg HMul.hMul EQ3) (f.divMonomial (g.toMonomial g_ismon))
    exact
      Eq.symm
        (Mathlib.Tactic.Abel.subst_into_add (g * f.divMonomial (g.toMonomial g_ismon))
          (f.modMonomial (g.toMonomial g_ismon))
          ((monomial (g.toMonomial g_ismon)) 1 * f.divMonomial (g.toMonomial g_ismon))
          (f.modMonomial (g.toMonomial g_ismon)) f EQ2 rfl EQ)
  . rw [leading_monomial, monomials]
    rw [toMonomial]
    have ⟨m0, ⟨m0P1, m0P2⟩⟩ := g_ismon
    have EQ4 : (Finset.choose (fun x ↦ True) g.support g_ismon = m0) := by
      have EQ5 := (@Finset.choose_mem _ (fun _ ↦ True) _ g.support g_ismon)
      apply m0P2
      exact Finset.choose_spec (fun x ↦ True) g.support g_ismon
    rw [EQ4]
    rcases em (f.modMonomial m0 = 0) with p | p
    . exact Or.symm (Or.inr p)
    . right
      intro m SUP DVD
      unfold monomials at DVD
      have LE : (m0 <= m) := by
        rw [Monomial.instDvd_equiv] at DVD
        rw [Monomial.instDvd_equiv'] at DVD
        rw [Monomial.instDvd''] at DVD
        -- have EQ5 : (@Finsupp.toFun σ _ LinearOrderedCommMonoidWithZero.toZero (@Finset.max' (Monomial σ) MonomialOrder.toLinearOrder g.support) = m0) := by
        --   sorry
        sorry
      have EQ5 := (@coeff_modMonomial_of_le _ _ _ _ _ f LE)
      have EQ6 := (Finsupp.mem_support_toFun (f.modMonomial m0) m).mp
      exact EQ6 SUP EQ5

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

lemma MvPolynomial.multidiv_correct [DecidableEq σ] [DecidableEq R] [LinearOrder σ] [ord : MonomialOrder σ] [Field R] (s : MvPolynomial σ R) (F : Finset (MvPolynomial σ R)) (F_isMonomial : ∀ f ∈ F, is_monomial f):
    -- let (a,r) := (MvPolynomial.multidiv s F F_isMonomial);
    s = (s.multidiv F F_isMonomial).snd + (∑ (f ∈ F), ((s.multidiv F F_isMonomial).fst f)*(f)) /\
    ((s.multidiv F F_isMonomial).snd = 0 ∨ ∀m ∈ monomials (s.multidiv F F_isMonomial).snd, ∀ f (inF : f ∈ F), ¬ Monomial.instDvd.dvd (leading_monomial f (is_monomial_nonzero (F_isMonomial f inF))) m) := by sorry
  -- unfold multidiv; simp
  -- constructor
  -- .
  --   -- have F_isMonomial' := FList_isMonomial F F_isMonomial
  --   have : ∀ l (s : FiniteVarPoly σ R) F F_isMonomial (EQ: l = toList F), s = (multidiv_help s l (by rw[EQ]; exact FList_isMonomial F F_isMonomial)).2 + (∑ (f ∈ F), ((multidiv_help s l (by rw[EQ]; exact FList_isMonomial F F_isMonomial)).1 f)*(f)) := by
  --     clear s F F_isMonomial
  --     intro l s F F_isMonomial EQ
  --     have F_isMonomial' := FList_isMonomial F F_isMonomial
  --     rw [← EQ] at F_isMonomial'
  --     -- replace (FList_isMonomial F F_isMonomial) := F_isMonomial'
  --     -- clear F_isMonomial
  --     have EQ' : F = l.toFinset := by
  --       rw [EQ]; symm; unfold toList; apply Finset.sort_toFinset
  --     -- rw [EQ']
  --     have G : ∀ l (s : FiniteVarPoly σ R) (l_isMonomial := l.all fun f ↦ decide (f ≠ 0)), s = (s.multidiv_help l sorry).2 + (l.map (fun f => (s.multidiv_help l sorry).1 f * f)).sum := by
  --       intro l; induction' l with f F' IH
  --       <;> intro s l_isMonomial
  --       . unfold multidiv_help; simp
  --         rw [@List.sum_nil]
  --         have : F = ∅ := by
  --           apply Finset.eq_empty_of_forall_not_mem
  --           intro f
  --           have EQ' : ¬ ∃(f : FiniteVarPoly σ R), f ∈ toList F := by
  --             rw [← EQ]
  --             rintro ⟨f,h1,h2⟩
  --           by_contra G; apply EQ'
  --           exists f; unfold toList; rw [Finset.mem_sort]; assumption
  --         rw [this, Finset.sum_eq_fold]; simp;
  --         clear this EQ F_isMonomial F
  --         FiniteVarPoly is CommRing
  --         sorry
  --       . simp [multidiv_help]
  --         have IH' := IH (div s f (by sorry)).2 F'
  --         sorry
  --   apply this; rfl; assumption
