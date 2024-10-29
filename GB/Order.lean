import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Lex

section Monomial

def MonomialType (σ : Type) : Type := σ  →₀ ℕ

noncomputable instance MonomialType.instMul {σ : Type} : Mul (MonomialType σ) where
  mul := Finsupp.instAdd.add

-- noncomputable instance : CoeFun (MonomialType σ) (λ_ => σ -> ℕ) where
--   coe :=  fun f => f.toFun
-- noncomputable instance : Coe (MonomialType σ) (σ  →₀ ℕ) where
--   coe :=  fun f => f
-- noncomputable instance : CoeFun (σ  →₀ ℕ) (λ_ => σ -> ℕ) where
--   coe :=  fun f => f.toFun
noncomputable instance : FunLike (MonomialType σ) σ ℕ :=
  ⟨Finsupp.toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm ⟩

lemma add_apply (a b: MonomialType σ) (x: σ) : (a * b) x = a x + b x := by rfl

class MonomialOrder (σ : Type) extends (LinearOrder (MonomialType σ)) where
  respect : ∀(u v w : @MonomialType σ),  u < v -> u*w < v*w
  isWellOrder : IsWellOrder (MonomialType σ) (fun x y => x < y)

-- lexicographic order in monomial order
def lexHelp (σ : Type) [LinearOrder σ] : LinearOrder (MonomialType σ) :=
  @Finsupp.Lex.linearOrder σ Nat _ _ Nat.instLinearOrder

def lex_refl (u: MonomialType σ) : ofLex u = u := by rfl

lemma lex_ord_respect [LinearOrder σ] (u v w : MonomialType σ) :
  (lexHelp σ).lt u v → (lexHelp σ).lt (u * w) (v * w) := by
    intro uvlt
    rcases uvlt with ⟨x₁, h1, h2⟩
    rw [lex_refl, lex_refl] at h1
    rw [lex_refl, lex_refl] at h2
    constructor; constructor
    any_goals exact x₁
    . intro x₂ h3
      rw [lex_refl, lex_refl]
      have h4 := h1 x₂ h3
      rw [add_apply, add_apply]
      rw [h4]
    . rw [lex_refl, lex_refl]; simp
      rw [add_apply, add_apply]
      exact Nat.add_lt_add_right h2 (w x₁)

instance lex_isWellOrder [LinearOrder σ] : IsWellOrder (MonomialType σ) fun x y ↦ (lexHelp σ).lt x y := by
  sorry

def lex (σ : Type) [LinearOrder σ] : MonomialOrder σ where
  le := (lexHelp σ).le
  le_refl := (lexHelp σ).le_refl
  le_trans := (lexHelp σ).le_trans
  le_antisymm := (lexHelp σ).le_antisymm
  le_total := (lexHelp σ).le_total
  decidableLE := (lexHelp σ).decidableLE
  respect := lex_ord_respect
  compare := (lexHelp σ).compare
  decidableEq := (lexHelp σ).decidableEq
  isWellOrder := lex_isWellOrder
  lt_iff_le_not_le := by
    intros a b
    exact (lexHelp σ).lt_iff_le_not_le a b
  compare_eq_compareOfLessAndEq := by
    intros a b
    exact (lexHelp σ).compare_eq_compareOfLessAndEq a b

def monomials [Field R] (p : MvPolynomial σ R) : Finset (MonomialType σ) :=
  p.support

def term_exists [Field R] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) : p.support.Nonempty := by
  exact (Finsupp.support_nonempty_iff.mpr p_nonzero)

def leading_monomial {R} [Field R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): MonomialType σ :=
  @Finset.max' _ ord.toLinearOrder p.support (term_exists p p_nonzero)

def leading_coeff {R} [Field R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): R :=
  MvPolynomial.coeff (leading_monomial p p_nonzero) p
