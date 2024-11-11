import GB.CFinsupp
import GB.Monomial
open Monomial

-- Finite Variable Polynomial
def FiniteVarPoly (σ : Type) (R : Type) [CommRing R] := CFinsupp (Monomial σ) R

noncomputable def ofFiniteVarPoly [DecidableEq σ] [CommRing R] : Coe (FiniteVarPoly σ R) (MvPolynomial σ R) where
  coe m := Finsupp.mapDomain ofCFinsupp.coe (ofCFinsupp.coe m)

noncomputable def toFiniteVarPoly [DecidableEq σ] [CommRing R] : Coe (MvPolynomial σ R) (FiniteVarPoly σ R) where
  coe m := toCFinsupp.coe (Finsupp.mapDomain toCFinsupp.coe m)

instance [DecidableEq σ] [CommRing R] [NeZero (1:R)] :
    Coe (Monomial σ) (FiniteVarPoly σ R) where
  coe := fun m => {
    support := {m}
    toFun := fun _ => 1
    nonzero := by intro; simp
  }

instance FiniteVarPoly.instAdd [DecidableEq σ] [DecidableEq R] [CommRing R] : Add (FiniteVarPoly σ R) where
  add := CFinsupp.binop' (fun (x y : R) => x+y)

instance FiniteVarPoly.instSub [DecidableEq σ] [DecidableEq R] [CommRing R] : Sub (FiniteVarPoly σ R) where
  sub := CFinsupp.binop' (fun (x y : R) => x+y)


instance MvPolynomial.instFunLike [DecidableEq σ] [CommRing R] : FunLike (MvPolynomial σ R) (σ→₀ℕ) R where
  coe m := m.toFun
  coe_injective' := Finsupp.instFunLike.2

instance FiniteVarPoly.instLinearOrder [DecidableEq σ] [DecidableEq R] [CommRing R] [LinearOrder σ] [LinearOrder R] : LinearOrder (FiniteVarPoly σ R) :=
  @CFinsuppInstLinearOrder (Monomial σ) R _ _ _ Monomial_lex _

def FiniteVarPoly.toList [DecidableEq σ] [DecidableEq R] [CommRing R] [LinearOrder σ] [LinearOrder R] (s : Finset (FiniteVarPoly σ R)) : List (FiniteVarPoly σ R) :=
  Finset.sort (FiniteVarPoly.instLinearOrder.le) s
