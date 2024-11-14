-- import GB.CFinsupp
import GB.Monomial
import GB.Polynomial
import GB.S_Poly
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic


section Reduction
variable
[DecidableEq (Monomial σ )]

-- Reduction Procedure, aka multivariate divison algorithm
def Generators (σ R: Type) [DecidableEq σ] [CommRing R] : Type := Finset (MvPolynomial σ R)

instance Generators.instMembership (σ R: Type) [DecidableEq σ] [CommRing R] : Membership (MvPolynomial σ R) (Generators σ R) where
  mem := Finset.instMembership.mem

-- def Monomial.div [DecidableEq σ] [CommRing R] (f : Monomial σ) (g : Monomial σ) (g_nonzero : g ≠ 0) : (Monomial σ) × (Monomial σ) :=


-- def MvPolynomial.div [DecidableEq σ] [Field R] (f : MvPolynomial σ R) (g : Monomial σ) (g_nonzero : g ≠ 0) : (MvPolynomial σ R) × (MvPolynomial σ R) :=
--   sorry

-- lemma MvPolynomial.div_correct [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (f : MvPolynomial σ R) (g : Monomial σ) (g_nonzero : g ≠ 0):
--   let (h,r) := MvPolynomial.div f g g_nonzero;
--   f = g*h+r ∧
--   (r = 0 ∨ ∀m ∈ monomials r, ¬ Monomial.instDvd.dvd (@leading_monomial σ _ _ _ ord g g_nonzero) m) := sorry

def FiniteVarPoly.multidiv_help [DecidableEq σ] [DecidableEq R] [LinearOrder σ] [LinearOrder R] [Field R] (s : MvPolynomial σ R) (F : List (Monomial σ)) (F_nonzero : F.all (fun f ↦ f≠0)): (Finsupp (MvPolynomial σ R) (MvPolynomial σ R)) × (MvPolynomial σ R) :=
  sorry
  -- match F with
  -- | [] => (CFinsupp.empty _ _, s)
  -- | f :: F' =>
  --   -- simp at F_nonzero; rcases F_nonzero with ⟨nonzero₁, nonzero₂⟩
  --   let (h₁,r) := div s f (by simp at F_nonzero; rcases F_nonzero; assumption)
  --   let (h₂,r) := multidiv_help r F' (by simp; simp at F_nonzero; rcases F_nonzero; assumption)
  --   (if p: h₁≠0 then CFinsupp_add h₂ f h₁ p else h₂, r)

lemma FList_nonzero [DecidableEq σ] [DecidableEq R] [LinearOrder σ] [LinearOrder R] [Field R] (F : Generators σ R) (F_nonzero : ∀ f ∈ F, f ≠ 0) : (MvPolynomial.toList F).all (fun f ↦ f≠0) := by
  sorry
  -- have mem_sort : ∀ f, f ∈ FiniteVarPoly.toList F ↔ f ∈ F := by
  --   intro f; rw [FiniteVarPoly.toList, Finset.mem_sort]
  -- rw [List.all_eq]
  -- rcases em (∀ x ∈ FiniteVarPoly.toList F, decide (x ≠ 0) = true) with e1|e1 <;> simp [e1] <;>
  -- intro x h <;> rw [mem_sort] at h <;> apply F_nonzero <;> assumption

def FiniteVarPoly.multidiv [DecidableEq σ] [DecidableEq R] [LinearOrder σ] [LinearOrder R] [Field R] (s : MvPolynomial σ R) (F : Generators σ R) (F_nonzero : ∀ f ∈ F, f ≠ 0) :
    (Finsupp (MvPolynomial σ R) (MvPolynomial σ R)) × (MvPolynomial σ R) := by sorry

lemma FiniteVarPoly.multidiv_correct [DecidableEq σ] [DecidableEq R] [LinearOrder σ] [LinearOrder R] [ord : MonomialOrder σ] [Field R] (s : MvPolynomial σ R) (F : Generators σ R) (F_nonzero : ∀ f ∈ F, f ≠ 0):
    let (a,r) := FiniteVarPoly.multidiv s F F_nonzero;
    s = r + (∑ (f ∈ F), (a f)*(f)) /\
    (r = 0 ∨ ∀m ∈ monomials r, ∀ f (inF : f ∈ F), ¬ Monomial.instDvd.dvd (leading_monomial f (F_nonzero f inF)) m) := by sorry
  -- unfold multidiv; simp
  -- constructor
  -- .
  --   -- have F_nonzero' := FList_nonzero F F_nonzero
  --   have : ∀ l (s : FiniteVarPoly σ R) F F_nonzero (EQ: l = toList F), s = (multidiv_help s l (by rw[EQ]; exact FList_nonzero F F_nonzero)).2 + (∑ (f ∈ F), ((multidiv_help s l (by rw[EQ]; exact FList_nonzero F F_nonzero)).1 f)*(f)) := by
  --     clear s F F_nonzero
  --     intro l s F F_nonzero EQ
  --     have F_nonzero' := FList_nonzero F F_nonzero
  --     rw [← EQ] at F_nonzero'
  --     -- replace (FList_nonzero F F_nonzero) := F_nonzero'
  --     -- clear F_nonzero
  --     have EQ' : F = l.toFinset := by
  --       rw [EQ]; symm; unfold toList; apply Finset.sort_toFinset
  --     -- rw [EQ']
  --     have G : ∀ l (s : FiniteVarPoly σ R) (l_nonzero := l.all fun f ↦ decide (f ≠ 0)), s = (s.multidiv_help l sorry).2 + (l.map (fun f => (s.multidiv_help l sorry).1 f * f)).sum := by
  --       intro l; induction' l with f F' IH
  --       <;> intro s l_nonzero
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
  --         clear this EQ F_nonzero F
  --         FiniteVarPoly is CommRing
  --         sorry
  --       . simp [multidiv_help]
  --         have IH' := IH (div s f (by sorry)).2 F'
  --         sorry
  --   apply this; rfl; assumption
