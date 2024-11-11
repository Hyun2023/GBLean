import GB.CFinsupp
import GB.Monomial
import GB.Polynomial
import GB.S_Poly
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic

-- Reduction Procedure, aka multivariate divison algorithm
def Generators (σ R: Type) [DecidableEq σ] [CommRing R] : Type := Finset (FiniteVarPoly σ R)

instance Generators.instMembership (σ R: Type) [DecidableEq σ] [CommRing R] : Membership (FiniteVarPoly σ R) (Generators σ R) where
  mem := Finset.instMembership.mem

def FiniteVarPoly.div [DecidableEq σ] [Field R] (f g : FiniteVarPoly σ R) (g_nonzero : g ≠ 0) : (FiniteVarPoly σ R) × (FiniteVarPoly σ R) := sorry

lemma FiniteVarPoly.div_correct [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (f g : FiniteVarPoly σ R) (g_nonzero : g ≠ 0):
  let (h,r) := FiniteVarPoly.div f g g_nonzero;
  f = g*h+r ∧
  (r = 0 ∨ ∀m ∈ monomials r, ¬ Monomial.instDvd.dvd (leading_monomial g g_nonzero) m) := sorry

def FiniteVarPoly.multidiv_help [DecidableEq σ] [DecidableEq R] [LinearOrder σ] [LinearOrder R] [Field R] (s : FiniteVarPoly σ R) (F : List (FiniteVarPoly σ R)) (F_nonzero : F.all (fun f ↦ f≠0)): (CFinsupp (FiniteVarPoly σ R) (FiniteVarPoly σ R)) × (FiniteVarPoly σ R) :=
  match F with
  | [] => (CFinsupp.empty _ _, s)
  | List.cons f F' => by
    simp at F_nonzero; rcases F_nonzero with ⟨nonzero₁, nonzero₂⟩
    have (h₁,r) := div s f nonzero₁
    have (h₂,r) := multidiv_help r F' (by simp; exact nonzero₂)
    exact (if p: h₁≠0 then CFinsupp_add h₂ f h₁ p else h₂, r)

def FiniteVarPoly.multidiv [DecidableEq σ] [DecidableEq R] [LinearOrder σ] [LinearOrder R] [Field R] (s : FiniteVarPoly σ R) (F : Generators σ R) (F_nonzero : ∀ f ∈ F, f ≠ 0) :
    (CFinsupp (FiniteVarPoly σ R) (FiniteVarPoly σ R)) × (FiniteVarPoly σ R) := by
  have FList := toList F
  have mem_sort : ∀ f, f ∈ toList F ↔ f ∈ F := by
    intro f; rw [toList, Finset.mem_sort]
  have FList_nonzero : FList.all (fun f ↦ f≠0) := by
    induction' FList with hd tl h
    . rw [List.all_nil]
    . rw [List.all_cons, h]; simp; apply F_nonzero; rw [← mem_sort]
      sorry
  exact multidiv_help s FList FList_nonzero

lemma FiniteVarPoly.multidiv_correct [DecidableEq σ] [DecidableEq R] [LinearOrder σ] [LinearOrder R] [ord : MonomialOrder σ] [Field R] (f : FiniteVarPoly σ R) (F : Generators σ R) (F_nonzero : ∀ f ∈ F, f ≠ 0):
    let (a,r) := FiniteVarPoly.multidiv f F F_nonzero;
    f = r + (∑ (f ∈ F), (a f)*(f)) /\
    (r = 0 ∨ ∀m ∈ monomials r, ∀ (inF : f ∈ F), ¬ Monomial.instDvd.dvd (leading_monomial f (F_nonzero f inF)) m) := sorry
