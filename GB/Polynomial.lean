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
  sub := CFinsupp.binop' (fun (x y : R) => x-y)

def zeropoly [DecidableEq σ] [CommRing R] : FiniteVarPoly σ R :=
  ⟨Finset.empty, fun _ => 0, by
    rintro ⟨x,_,_⟩
  ⟩

-- def term_exists2 [DecidableEq σ] [CommRing R] (p : FiniteVarPoly σ R) (p_nonzero : ¬CFinsuppequiv p zeropoly) : (CFinsupp.support p).Nonempty := by
--   by_contra NE
--   apply p_nonzero
--   unfold CFinsuppequiv
--   constructor
--   .
--   .
--   apply funext

-- def leading_monomial2 [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : FiniteVarPoly σ R) (p_nonzero : p ≠ zeropoly): Monomial σ :=
--   @Finset.max' _ ord.toLinearOrder (CFinsupp.support p)
--   (term_exists2 p p_nonzero)

def leading_monomial2 [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : FiniteVarPoly σ R) (p_nonzero : (CFinsupp.support p).Nonempty): Monomial σ :=
  @Finset.max' _ ord.toLinearOrder (CFinsupp.support p)
  p_nonzero
