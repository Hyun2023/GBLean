import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finset.Basic
import GB.CFinsupp

section Monomial

-- Definition of Monomial and related operation
def Monomial (σ : Type) := Finsupp σ ℕ

def MonomialExists : (Inhabited (Monomial σ)) := by
  constructor;exact Finsupp.instInhabited.default

-- instance ofMonomial [DecidableEq σ] : Coe (Monomial σ) (Finsupp σ ℕ) where
--   coe := λ x => x

-- instance toMonomial [DecidableEq σ] : Coe (σ →₀ ℕ) (Monomial σ) where
--   coe := λ x => x

instance Monomial.Zero : Zero (Monomial σ) where
  zero := Finsupp.instZero.zero

noncomputable instance Monomial.toMvPolynomial [DecidableEq σ] [CommRing R] : Coe (Monomial σ) (MvPolynomial σ R) where
  coe := fun m => MvPolynomial.monomial m 1

noncomputable def toMvPolynomial [CommRing R] (m : Monomial σ) : (MvPolynomial σ R) :=
  MvPolynomial.monomial m 1

-- def toMvPolynomial_preserves_nonzero [CommRing R] (m : Monomial σ) (m_nonzero : m ≠ 0) : (@toMvPolynomial R σ _ m) ≠ 0 := by
--   intro H
--   rw [toMvPolynomial, MvPolynomial.monomial] at H
--   rw [Finsupp.lsingle] at H; dsimp at H
--   sorry

noncomputable instance Monomial.instMul : Mul (Monomial σ) where
  mul := fun m1 m2 => Finsupp.instAdd.add m1 m2

noncomputable def LCM : Monomial σ → Monomial σ → Monomial σ :=
  fun m1 m2 => Finsupp.zipWith (Nat.max) (by rfl) m1 m2

-- def LCM_computable [DecidableEq σ] : Computable₂ (@LCM σ) := by
--   sorry

noncomputable instance Monomial.instDiv [DecidableEq σ] : Div (Monomial σ) where
  div m1 m2 := Finsupp.zipWith (Nat.sub) (by rfl) m1 m2

instance Monomial.instDvd [DecidableEq σ] : Dvd (Monomial σ) where
  dvd f g :=
    ∃ k, g= f*k

-- f is divisible by g
def Monomial.instDvd' [DecidableEq σ] (f g : Monomial σ) : Prop :=
  (f.support ⊆ g.support) ∧ (∀ (x : σ) (GS : x ∈ f.support), f.toFun x <= g.toFun x)

def Monomial.instDvd'' [DecidableEq σ] (f g : Monomial σ) : Prop :=
  f.toFun <= g.toFun

instance Monomial.instDvd'_decidable [DecidableEq σ] (f g : Monomial σ) : Decidable (Monomial.instDvd' f g) := by
  rw [instDvd']
  apply instDecidableAnd

def Monomial.instDvd'_div [DecidableEq σ] (f g : Monomial σ) (Dvd' : Monomial.instDvd' f g):
  g = f * (g / f) := by
  rw [instDvd'] at Dvd'
  obtain ⟨_, H2⟩ := Dvd'
  rw [HDiv.hDiv, instHDiv]; simp
  rw [Div.div, instDiv]; simp
  rw [HMul.hMul, instHMul]; simp
  rw [Mul.mul, instMul]; simp
  rw [Add.add, Finsupp.instAdd]; simp
  apply Finsupp.ext
  intro a; simp
  rcases em (a ∈ f.support) with h|h
  . exact Eq.symm (Nat.add_sub_of_le (H2 a h))
  . simp at h; rw [h]
    exact Eq.symm (Nat.zero_add (g.toFun a - 0))

def Monomial.instDvd_equiv [DecidableEq σ] (f g : Monomial σ) :
  f ∣ g <-> Monomial.instDvd' f g := by
  rw [Dvd.dvd, instDvd]; simp
  constructor <;> intro H
  . obtain ⟨k, EQ⟩ := H
    rw [EQ, HMul.hMul, instHMul]; simp
    rw [Mul.mul, instMul]; simp
    rw [Add.add, Finsupp.instAdd]; simp
    rw [Finsupp.zipWith, Finsupp.onFinset]; simp
    constructor
    . rw [Finset.subset_iff]
      intro x GS
      simp
      constructor
      . have SUPP := (Finsupp.mem_support_toFun f x)
        rw [SUPP] at GS
        left
        intro H
        exact GS H
      . intro H
        exfalso
        have SUPP := (Finsupp.mem_support_toFun f x)
        rw [SUPP] at GS
        exact GS H
    . intro x _
      apply Nat.le_add_right
  . use (g / f)
    apply Monomial.instDvd'_div
    exact H

def Monomial.instDvd_equiv' [DecidableEq σ] (f g : Monomial σ) :
  Monomial.instDvd' f g <-> Monomial.instDvd'' f g := by
  rw [instDvd', instDvd'']; simp
  constructor <;> intro H
  . apply Pi.le_def.mpr
    intro x
    rcases em (f.toFun x = 0) with p|p
    . exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a ↦ a) p (g.toFun x)
    . obtain ⟨SUP, LE⟩ := H
      apply LE _ p
  . constructor
    . exact Finsupp.support_mono H
    . intro x H'
      apply H

-- Monomial Order
class MonomialOrder (σ : Type) [DecidableEq σ] extends (LinearOrder (Monomial σ)) where
  respect : ∀(u v w : @Monomial σ),  u < v -> u*w < v*w
  isWellOrder : IsWellOrder (Monomial σ) (fun x y => x < y)
  decidableOrder : ∀(u v : @Monomial σ), Decidable (u < v)


-- def Monomial_lex [DecidableEq σ] [LinearOrder σ] : LinearOrder (Monomial σ) :=
--   CFinsuppInstLinearOrder

def monomials [DecidableEq σ] [CommRing R] (p : MvPolynomial σ R) : Finset (Monomial σ) :=
  p.support


-- Leading Monomial and Term
def term_exists [DecidableEq σ] [CommRing R] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) : (monomials p).Nonempty := by
  have exM : exists m, MvPolynomial.coeff m p ≠ 0 := by
    rw [MvPolynomial.ne_zero_iff] at p_nonzero
    exact p_nonzero
  rcases exM with ⟨m, mcond⟩
  constructor; any_goals exact m
  rw [monomials]
  rw [MvPolynomial.coeff] at mcond; simp at mcond
  apply (p.mem_support_toFun m).mpr mcond

def leading_monomial_option [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) : Option (Monomial σ) :=
  @Finset.max _ ord.toLinearOrder (monomials p)

def leading_monomial [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): Monomial σ :=
  @Finset.max' _ ord.toLinearOrder (monomials p)
  (term_exists p p_nonzero)

-- -- If p is zero, it gives runtime error. Wait, runtime error in proof assistant?
def leading_monomial_unsafe [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) : (Monomial σ) :=
  @Option.get! _ MonomialExists (@Finset.max _ ord.toLinearOrder (monomials p))

lemma leading_monomial_in [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) :
  leading_monomial p p_nonzero ∈ p.support := by
  unfold leading_monomial
  unfold monomials
  apply Finset.max'_mem

lemma leading_monomial_sound [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0)
  (m : Monomial σ) (m_in : m ∈ p.support) :
  m ≤ leading_monomial p p_nonzero := by
  unfold leading_monomial
  unfold monomials
  apply Finset.le_max'
  assumption

def leading_coeff [DecidableEq σ] [CommRing R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) : R :=
  MvPolynomial.coeff (leading_monomial p p_nonzero) p

lemma leading_coeff_nonzero [DecidableEq σ] [CommRing R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) :
  leading_coeff p p_nonzero ≠ 0 := by
  unfold leading_coeff
  apply (@Finsupp.mem_support_iff _ _ _ p (leading_monomial p p_nonzero)).mp
  apply leading_monomial_in
