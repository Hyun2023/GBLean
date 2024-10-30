import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finset.Basic



-- Definition of Monomial and related operation
def Monomial (σ : Type) : Type := σ  →₀ ℕ

noncomputable instance Monomial.instMul : Mul (Monomial σ) where
  mul := fun f g => Finsupp.instAdd.add f g

noncomputable instance [Field R] : Coe (Monomial σ) (MvPolynomial σ R) where
  coe := fun m => MvPolynomial.monomial m 1

noncomputable def LCM (f g :Monomial σ) : (Monomial σ) := by
  have hf : Nat.max 0 0 = 0 := by rfl
  exact Finsupp.zipWith Nat.max hf f g


-- Monomial Order
class MonomialOrder (σ : Type) extends (LinearOrder (@Monomial σ)) where
  respect : ∀(u v w : @Monomial σ),  u < v -> u*w < v*w

def monomials [Field R] (p : MvPolynomial σ R) : Finset (Monomial σ) :=
  p.support


-- Leading Monomial and Term
def term_exists [Field R] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) : p.support.Nonempty := by
  exact (Finsupp.support_nonempty_iff.mpr p_nonzero)

def leading_monomial {R} [Field R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): Monomial σ :=
  @Finset.max' _ ord.toLinearOrder p.support (term_exists p p_nonzero)

def leading_coeff {R} [Field R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): R :=
  MvPolynomial.coeff (leading_monomial p p_nonzero) p
