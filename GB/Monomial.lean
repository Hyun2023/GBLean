import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finset.Basic



-- Definition of Monomial and related operation
def Monomial (σ : Type) : Type := (X: Finset σ) × (X → ℕ)

def MonomialExists : (Inhabited (Monomial σ)) := ⟨Finset.empty, fun _ => 0⟩

instance Monomial.instMul [DecidableEq σ] : Mul (Monomial σ) where
  mul f g := ⟨f.1 ∪ g.1, by
    intros x; rcases x with ⟨x, infg⟩
    have ite (f: Monomial σ) (v1 : (x∈f.1) → ℕ) (v2 : (x∉f.1) → ℕ) : ℕ :=
      Decidable.casesOn (Finset.decidableMem x f.1) v2 v1
    apply (ite f) <;> intro pf
    . apply (ite g) <;> intro pg
      -- x∈f.1 && x∈g.1, return f.2 x + g.2 x
      . apply Nat.add
        . apply f.2; constructor; exact pf
        . apply g.2; constructor; exact pg
      -- x∈f.1 && x∉g.1, return f.2 x
      . apply f.2; constructor; exact pf
    . apply (ite g) <;> intro pg
      -- x∉f.1 && x∈g.1, return g.2 x
      . apply g.2; constructor; exact pg
      -- x∉f.1 && x∉g.1, contradicton
      . have : x ∉ f.fst ∪ g.fst := by
          refine Finset.not_mem_union.mpr ?_
          constructor <;> assumption
        contradiction
  ⟩

-- def Finset.ofSet (A : Finset (Finset T)) : Finset T := by
--   rcases A with ⟨A,P⟩
--   rcases A
--   constructor

-- def asdfdsf (x: Set (Finset T)) : Finset T := by apply? using x

-- instance setFintypeSet (m : Monomial σ) : Fintype ↑(m ⁻¹' fun x ↦ x ≠ 1) := by sorry

noncomputable instance : Coe (Monomial σ) (σ →₀ ℕ) where
  -- coe := fun m => ⟨@Set.toFinset (Finset σ) (m ⁻¹' (fun x => x≠1)) (setFintypeSet m), sorry, sorry⟩
  coe := fun m => ⟨sorry, sorry, sorry⟩

noncomputable instance : Coe (σ →₀ ℕ) (Monomial σ) where
  coe := fun m x => Finsupp.toFun m x

noncomputable instance [CommRing R] : Coe (Monomial σ) (MvPolynomial σ R) where
  coe := fun m => MvPolynomial.monomial m 1

noncomputable def LCM (f g :Monomial σ) : (Monomial σ) := fun x => Nat.max (f x) (g x)


-- Monomial Order
class MonomialOrder (σ : Type) extends (LinearOrder (Monomial σ)) where
  respect : ∀(u v w : @Monomial σ),  u < v -> u*w < v*w
  isWellOrder : IsWellOrder (Monomial σ) (fun x y => x < y)

def monomials [CommRing R] (p : MvPolynomial σ R) : Finset (Monomial σ) :=
  p.support


-- Leading Monomial and Term
def term_exists [CommRing R] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) : p.support.Nonempty := by
  exact (Finsupp.support_nonempty_iff.mpr p_nonzero)

def leading_monomial {R} [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): Monomial σ :=
  @Finset.max' _ ord.toLinearOrder p.support (term_exists p p_nonzero)

-- If p is zero, it gives runtime error. Wait, runtime error in proof assistant?
def leading_monomial_unsafe {R} [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) : (Monomial σ) :=
  @Option.get! _ MonomialExists (@Finset.max _ ord.toLinearOrder p.support)

def leading_coeff {R} [CommRing R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): R :=
  MvPolynomial.coeff (leading_monomial p p_nonzero) p


-- Finite Variable Polynomial
structure FinteVarPoly [CommRing R] (n : ℕ) where
  vars := Finset.range n
  monomials : Finset (vars -> ℕ)
  poly : monomials -> R


def FinsetSuppIsFinsupp [DecidableEq A] [DecidableEq B] [Zero B] (A' : Finset A) (f : A' -> B) : Finsupp A B:=
  let lift := fun x :A => if h: x ∈ A' then f ⟨x,h⟩ else 0
  {
    support := A'.filter (fun x : A => lift x ≠ 0 )
    toFun := lift
    mem_support_toFun := by
    {
      intros x
      constructor
      simp
      {
        simp
        intros lftx
        constructor
        {
          by_cases h: x ∈ A'
          { exact h }
          {
            have hh : lift x =0 := by simp [h, lift]
            exfalso;apply lftx;exact hh
          }
        }
        {
          exact lftx
        }
      }
    }
  }
