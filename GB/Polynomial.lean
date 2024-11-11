import GB.CFinsupp
import GB.Monomial
open Monomial

-- Finite Variable Polynomial
def FiniteVarPoly (σ : Type) (R : Type) [CommRing R] := CFinsupp (Monomial σ) R

noncomputable instance ofFiniteVarPoly [DecidableEq σ] [CommRing R] : Coe (FiniteVarPoly σ R) (MvPolynomial σ R) where
  coe m := Finsupp.mapDomain ofCFinsupp.coe (ofCFinsupp.coe m)

noncomputable instance toFiniteVarPoly [DecidableEq σ] [CommRing R] : Coe (MvPolynomial σ R) (FiniteVarPoly σ R) where
  coe m := toCFinsupp.coe (Finsupp.mapDomain toCFinsupp.coe m)

lemma toFiniteVarPoly_ofFiniteVarPoly_inverse [DecidableEq σ] [CommRing R] : ∀ p, (@toFiniteVarPoly σ R _ _).coe (ofFiniteVarPoly.coe p) = p := by
  intro p; rw [Coe.coe, Coe.coe, toFiniteVarPoly, ofFiniteVarPoly]; simp
  rw [← Finsupp.mapDomain_comp]
  have H : ((@toCFinsupp σ ℕ _ _).coe ∘ (@ofCFinsupp σ ℕ _ _).coe = id) := by
    ext x; simp; rw [toCFinsupp_ofCFinsupp_inverse]
  rw [H]; simp
  rw [Coe.coe, Coe.coe]
  nth_rewrite 2 [← toCFinsupp_ofCFinsupp_inverse p, Coe.coe];
  rw [Coe.coe]

lemma ofFiniteVarPoly_toFiniteVarPoly_inverse [DecidableEq σ] [CommRing R] : ∀ p, (@ofFiniteVarPoly σ R _ _).coe (toFiniteVarPoly.coe p) = p := by
  sorry

instance FiniteVarPoly.instFunLike [DecidableEq σ] [CommRing R] : FunLike (FiniteVarPoly σ R) (Monomial σ) R := CFinsupp.instFunLike

instance MvPolynomial.instFunLike [DecidableEq σ] [CommRing R] : FunLike (MvPolynomial σ R) (σ→₀ℕ) R where
  coe m := m.toFun
  coe_injective' := Finsupp.instFunLike.2

lemma coeff_equiv [DecidableEq σ] [CommRing R] :
  ∀ (m : Monomial σ) (p : FiniteVarPoly σ R), @MvPolynomial.coeff R σ _ m p = p m := by
  intro m p; rw [MvPolynomial.coeff]; rw [Finsupp.mapDomain_apply]
  . simp; rcases (em (m ∈ p.support)) with h|h <;> simp [h]
    sorry
    sorry
  sorry

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

instance FiniteVarPoly.instLinearOrder [DecidableEq σ] [DecidableEq R] [CommRing R] [LinearOrder σ] [LinearOrder R] : LinearOrder (FiniteVarPoly σ R) :=
  @CFinsuppInstLinearOrder (Monomial σ) R _ _ _ Monomial_lex _

def FiniteVarPoly.toList [DecidableEq σ] [DecidableEq R] [CommRing R] [LinearOrder σ] [LinearOrder R] (s : Finset (FiniteVarPoly σ R)) : List (FiniteVarPoly σ R) :=
  Finset.sort (FiniteVarPoly.instLinearOrder.le) s

instance [DecidableEq σ] [DecidableEq R] [CommRing R] : DecidableEq (FiniteVarPoly σ R) := CFinsupp.DecidableEq

instance [CommRing R] : CommSemiring (FiniteVarPoly σ R) := sorry


def monomials [DecidableEq σ] [CommRing R] (p : FiniteVarPoly σ R) : Finset (Monomial σ) :=
  p.support

-- Leading Monomial and Term
def isZeroEquiv [DecidableEq σ] [CommRing R] :
    ∀ (m : FiniteVarPoly σ R), m = 0 ↔ (m : MvPolynomial σ R) = 0 := by
  -- intro m; constructor <;> intro h
  -- . subst h; rw [Coe.coe, ofFiniteVarPoly]; simp
  --   apply Finsupp.mapDomain_apply
  --   sorry
  sorry
def isNonZeroEquiv [DecidableEq σ] [CommRing R] :
    ∀ (m : FiniteVarPoly σ R), m ≠ 0 ↔ (m : MvPolynomial σ R) ≠ 0 := by
  intro m; constructor <;> intro h g <;> apply h
  rw [isZeroEquiv]; assumption
  rw [← isZeroEquiv]; assumption

def term_exists [DecidableEq σ] [CommRing R] (p : FiniteVarPoly σ R) (p_nonzero : p ≠ 0) : (monomials p).Nonempty := by
  -- have exM : exists m, p m ≠ 0 := by
  --   rw [Ne, isZeroEquiv, ← Ne] at p_nonzero
  --   rw [MvPolynomial.ne_zero_iff] at p_nonzero
  --   rcases p_nonzero with ⟨m, p_nonzero⟩
  --   exists m; simp; rw [coeff_equiv m] at p_nonzero
  --   exact p_nonzero
  -- rcases exM with ⟨m, mcond⟩
  -- constructor; any_goals exact (toMonomial.coe m)
  -- rw [monomials, toCFinsupp_emb]
  -- apply Finset.mem_map.mpr; simp
  -- exists (m)
  sorry

def leading_monomial [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : FiniteVarPoly σ R) (p_nonzero : p ≠ 0): Monomial σ :=
  @Finset.max' _ ord.toLinearOrder (monomials p)
  (term_exists p p_nonzero)

-- instance FiniteVarPoly.instMul [DecidableEq σ] [DecidableEq R] [CommRing R] : Mul (FiniteVarPoly σ R) where
--   mul :=

-- instance FiniteVarPoly_CommRing [CommRing R] : CommRing (FiniteVarPoly σ R) where

def zeropoly [DecidableEq σ] [CommRing R] : FiniteVarPoly σ R :=
  ⟨Finset.empty, fun _ => 0, by
    rintro ⟨x,_,_⟩
  ⟩

def term_exists2 [DecidableEq σ] [CommRing R] (p : FiniteVarPoly σ R) (p_nonzero : ¬CFinsuppequiv p zeropoly) : (CFinsupp.support p).Nonempty := by
  by_contra NE
  apply p_nonzero
  unfold CFinsuppequiv
  constructor
  . unfold zeropoly; simp
    rw [Finset.not_nonempty_iff_eq_empty] at NE
    rw [NE]
    rfl
  . intro a; intro in1; intro in2
    unfold zeropoly at in2; simp at in2
    exfalso
    apply Finset.not_mem_empty at in2
    apply in2

-- def leading_monomial2 [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : FiniteVarPoly σ R) (p_nonzero : p ≠ zeropoly): Monomial σ :=
--   @Finset.max' _ ord.toLinearOrder (CFinsupp.support p)
--   (term_exists2 p p_nonzero)

def leading_monomial2 [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : FiniteVarPoly σ R) (p_nonzero : (CFinsupp.support p).Nonempty): Monomial σ :=
  @Finset.max' _ ord.toLinearOrder (CFinsupp.support p)
  p_nonzero

-- def coeff2 [DecidableEq σ] [CommRing R] (p : FiniteVarPoly σ R)

def leading_coeff2 [DecidableEq σ] [CommRing R] [MonomialOrder σ ] (p : FiniteVarPoly σ R) (p_nonzero : (CFinsupp.support p).Nonempty): R :=
  p.toFun ⟨leading_monomial2 p p_nonzero, by
    unfold leading_monomial2
    apply Finset.max'_mem
  ⟩
