import GB.Monomial
import GB.Polynomial
import GB.S_Poly
import Mathlib.Algebra.MvPolynomial.Basic

-- Reduction Procedure, aka multivariate divison algorithm
structure Generators (σ R: Type) (size : ℕ) [DecidableEq σ] [CommRing R] : Type where
  gens : ℕ → (MvPolynomial σ R)
  bounded : ∀ i ≥ size, gens i = 0

instance Generators.FunLike [DecidableEq σ] [Field R] : FunLike (Generators σ R m) ℕ (MvPolynomial σ R) where
  coe := gens
  coe_injective' := by rintro ⟨_,_⟩ ⟨_,_⟩ _; congr!

def MvPolynomial.div [DecidableEq σ] [Field R] (f g : MvPolynomial σ R) (g_nonzero : g ≠ 0) : (MvPolynomial σ R) × (MvPolynomial σ R) := sorry

lemma MvPolynomial.div_correct [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (f g : MvPolynomial σ R) (g_nonzero : g ≠ 0):
  let (h,r) := MvPolynomial.div f g g_nonzero;
  f = g*h+r ∧
  (r = 0 ∨ ∀m ∈ monomials r, ¬ Monomial.instDvd.dvd (leading_monomial g g_nonzero) m) := sorry

def Mvpolynomial.multidiv [DecidableEq σ] [Field R] (f : MvPolynomial σ R) (F : Generators σ R s) (F_nonzero : ∀ i < s, F i ≠ 0) :
    (ℕ → MvPolynomial σ R) × (MvPolynomial σ R) :=
  sorry

lemma Mvpolynomial.multidiv_correct [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (f : MvPolynomial σ R) (F : Generators σ R s) (F_nonzero : ∀ i < s, F i ≠ 0):
    let (a,r) := Mvpolynomial.multidiv f F F_nonzero;
    ∀ i≥s, a i = 0 /\
    f = r + (∑ (i : {i | i<s}), (a i.1)*(F i.1)) /\
    (r = 0 ∨ ∀m ∈ monomials r, ∀ (ilt : i < s), ¬ Monomial.instDvd.dvd (leading_monomial (F i) (F_nonzero i ilt)) m) := sorry

def red [DecidableEq σ] [Field R] (f : MvPolynomial σ R) : MvPolynomial σ R := sorry
