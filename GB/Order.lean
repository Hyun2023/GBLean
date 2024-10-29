import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Lex

def MonomialType (σ : Type) : Type := σ  →₀ ℕ

noncomputable instance MonomialType.instMul {σ : Type} : Mul (@MonomialType σ) :=
  Finsupp.instMul

class MonomialOrder (σ : Type) extends (LinearOrder (@MonomialType σ)) where
  respect : ∀(u v w : @MonomialType σ),  u < v -> u*w < v*w

-- lexicographic order in monomial order
def lexHelp (σ : Type) [LinearOrder σ] : LinearOrder (@MonomialType σ) :=
  @Finsupp.Lex.linearOrder σ Nat _ _ Nat.instLinearOrder

def lex (σ : Type) [LinearOrder σ] : MonomialOrder σ where
  le := (lexHelp σ).le
  le_refl := (lexHelp σ).le_refl
  le_trans := (lexHelp σ).le_trans
  le_antisymm := (lexHelp σ).le_antisymm
  le_total := (lexHelp σ).le_total
  decidableLE := (lexHelp σ).decidableLE
  respect := by (
    intro u v w uvlt
    rcases uvlt with ⟨x₁, h1, h2⟩
    -- dsimp [mul]
    -- rw [Finsupp.toFun] at h2
    -- rw [ofLex, Equiv.refl] at h2; simp at h2
    constructor; constructor
    any_goals exact x₁
    -- intro x₂ h1; rw [ofLex, Finsupp.mul_apply]
    sorry
    sorry
  )
  compare := (lexHelp σ).compare
  decidableEq := (lexHelp σ).decidableEq

def monomials [Field R] (p : MvPolynomial σ R) : Finset (MonomialType σ) :=
  p.support

def term_exists [Field R] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) : p.support.Nonempty := by
  exact (Finsupp.support_nonempty_iff.mpr p_nonzero)

def leading_monomial {R} [Field R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): MonomialType σ :=
  @Finset.max' _ ord.toLinearOrder p.support (term_exists p p_nonzero)

def leading_coeff {R} [Field R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): R :=
  MvPolynomial.coeff (leading_monomial p p_nonzero) p
