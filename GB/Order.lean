import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finset.Basic

def MonomialType (σ : Type) : Type := σ  →₀ ℕ

noncomputable instance MonomialType.instMul {σ : Type} : Mul (@MonomialType σ) :=
  Finsupp.instMul

class MonomialOrder (σ : Type) extends (LinearOrder (@MonomialType σ)) where
  respect : ∀(u v w : @MonomialType σ),  u < v -> u*w < v*w

def monomials [Field R] (p : MvPolynomial σ R) : Finset (MonomialType σ) :=
  p.support

def term_exists [Field R] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) : p.support.Nonempty := by
  exact (Finsupp.support_nonempty_iff.mpr p_nonzero)

def leading_monomial {R} [Field R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): MonomialType σ :=
  @Finset.max' _ ord.toLinearOrder p.support (term_exists p p_nonzero)

def leading_coeff {R} [Field R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): R :=
  MvPolynomial.coeff (leading_monomial p p_nonzero) p
