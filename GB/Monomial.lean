import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finset.Basic
import GB.CFinsupp

section Monomial

-- Definition of Monomial and related operation
def Monomial (σ : Type)  := Finsupp σ ℕ

-- def MonomialExists : (Inhabited (Monomial σ)) := FinsuppExists

-- instance ofMonomial [DecidableEq σ] : Coe (Monomial σ) (Finsupp σ ℕ) where
--   coe := λ x => x

-- instance toMonomial [DecidableEq σ] : Coe (σ →₀ ℕ) (Monomial σ) where
--   coe := λ x => x

instance Monomial.Zero : Zero (Monomial σ) where
  zero := Finsupp.instZero.zero

noncomputable instance Monomial.toMvPolynomial [DecidableEq σ] [CommRing R] : Coe (Monomial σ) (MvPolynomial σ R) where
  coe := fun m => MvPolynomial.monomial m 1


noncomputable instance Monomial.instMul [DecidableEq σ] : Mul (Monomial σ) where
  mul := fun m1 m2 => Finsupp.instAdd.add m1 m2

noncomputable def LCM [DecidableEq σ] : Monomial σ → Monomial σ → Monomial σ :=
  fun m1 m2 => Finsupp.zipWith (Nat.max) (by rfl) m1 m2

-- instance Monomial.instDiv [DecidableEq σ] : Div (Monomial σ) where
--   div := CFinsupp.binop' Nat.sub

instance Monomial.instDvd [DecidableEq σ] : Dvd (Monomial σ) where
  dvd f g :=
    ∃ k, f= g*k

-- Monomial Order
class MonomialOrder (σ : Type) [DecidableEq σ] extends (LinearOrder (Monomial σ)) where
  respect : ∀(u v w : @Monomial σ),  u < v -> u*w < v*w
  isWellOrder : IsWellOrder (Monomial σ) (fun x y => x < y)
  decidableOrder : ∀(u v : @Monomial σ), Decidable (u < v)

-- def Monomial_lex [DecidableEq σ] [LinearOrder σ] : LinearOrder (Monomial σ) :=
--   CFinsuppInstLinearOrder

def monomials [DecidableEq σ] [CommRing R] (p : MvPolynomial σ R) : Finset (Monomial σ) :=
  p.support


-- -- Leading Monomial and Term
-- def term_exists [DecidableEq σ] [CommRing R] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) : (monomials p).Nonempty := by
--   have exM : exists m, MvPolynomial.coeff m p ≠ 0 := by
--     rw [MvPolynomial.ne_zero_iff] at p_nonzero
--     exact p_nonzero
--   rcases exM with ⟨m, mcond⟩
--   constructor; any_goals exact (toMonomial.coe m)
--   rw [monomials, toCFinsupp_emb]
--   apply Finset.mem_map.mpr; simp
--   exists (m)

def leading_monomial [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): Monomial σ :=
  @Finset.max' _ ord.toLinearOrder (monomials p)
  (sorry)

-- -- If p is zero, it gives runtime error. Wait, runtime error in proof assistant?
-- def leading_monomial_unsafe [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) : (Monomial σ) :=
--   @Option.get! _ MonomialExists (@Finset.max _ ord.toLinearOrder (monomials p))

-- def leading_coeff [DecidableEq σ] [CommRing R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): R :=
--   MvPolynomial.coeff (leading_monomial p p_nonzero) p
