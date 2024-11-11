import GB.CFinsupp
import GB.Monomial
import GB.Polynomial
import GB.S_Poly
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic

-- Reduction Procedure, aka multivariate divison algorithm
def Generators (σ R: Type) [DecidableEq σ] [CommRing R] : Type := Finset (MvPolynomial σ R)

instance Generators.instMembership (σ R: Type) [DecidableEq σ] [CommRing R] : Membership (MvPolynomial σ R) (Generators σ R) where
  mem := Finset.instMembership.mem

def MvPolynomial.div [DecidableEq σ] [Field R] (f g : MvPolynomial σ R) (g_nonzero : g ≠ 0) : (MvPolynomial σ R) × (MvPolynomial σ R) := sorry

lemma MvPolynomial.div_correct [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (f g : MvPolynomial σ R) (g_nonzero : g ≠ 0):
  let (h,r) := MvPolynomial.div f g g_nonzero;
  f = g*h+r ∧
  (r = 0 ∨ ∀m ∈ monomials r, ¬ Monomial.instDvd.dvd (leading_monomial g g_nonzero) m) := sorry

def Mvpolynomial.multidiv [DecidableEq σ] [Field R] (s : MvPolynomial σ R) (F : Generators σ R) (F_nonzero : ∀ f ∈ F, f ≠ 0) :
    (CFinsupp (MvPolynomial σ R) (MvPolynomial σ R)) × (MvPolynomial σ R) :=
  sorry

-- this will be replaced by CFinsupp.DecidableEq as MvPolynomial is replaced by FiniteVarPoly.
instance [DecidableEq σ] [CommRing R] : DecidableEq (MvPolynomial σ R) := sorry

lemma Mvpolynomial.multidiv_correct [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (f : MvPolynomial σ R) (F : Generators σ R) (F_nonzero : ∀ f ∈ F, f ≠ 0):
    let (a,r) := Mvpolynomial.multidiv f F F_nonzero;
    f = r + (∑ (f ∈ F), (a f)*(f)) /\
    (r = 0 ∨ ∀m ∈ monomials r, ∀ (inF : f ∈ F), ¬ Monomial.instDvd.dvd (leading_monomial f (F_nonzero f inF)) m) := sorry
