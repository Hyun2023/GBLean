import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finset.Basic



-- Definition of Monomial and related operation
structure Monomial (σ : Type) : Type where
  support : Finset σ
  toFun : support → ℕ
  nonzero : ∀x, toFun x ≠ 0

def MonomialExists : (Inhabited (Monomial σ)) :=
  ⟨Finset.empty, fun _ => 0, by
    rintro ⟨x,_,_⟩
  ⟩

lemma Finset.union_contradiction [DecidableEq σ] {A B : Finset σ} :
    (x ∉ A) -> (x ∉ B) -> x ∉ (A ∪ B) := by
  intro h1 h2
  apply Finset.not_mem_union.mpr
  constructor <;> assumption

instance Monomial.instMul [DecidableEq σ] : Mul (Monomial σ) where
  mul f g := ⟨
    f.1 ∪ g.1,
    fun ⟨x, infg⟩ =>
      if pf: x∈f.1 then
        if pg: x∈g.1 then (f.2 ⟨x, pf⟩ + g.2 ⟨x, pg⟩)
        else (f.2 ⟨x, pf⟩)
      else
        if pg: x∈g.1 then g.2 ⟨x, pg⟩
        else by
          have := Finset.union_contradiction pf pg
          contradiction,
    by
      simp; intro x infg G
      rcases em (x∈f.1) with pf|pf <;>
      rcases em (x∈g.1) with pg|pg <;>
      simp [pf, pg] at G
      . have nonzeroF := f.nonzero ⟨x,pf⟩
        rcases G; contradiction
      . have nonzeroF := f.nonzero ⟨x,pf⟩
        contradiction
      . have nonzeroG := g.nonzero ⟨x,pg⟩
        contradiction
      . rcases infg <;> contradiction
  ⟩

instance [DecidableEq σ] : Coe (Monomial σ) (σ →₀ ℕ) where
  coe := fun m => ⟨
    m.support,
    fun x => if p: x ∈ m.support then m.toFun ⟨x,p⟩  else 0,
    by
      intro x; constructor <;> intro h
      . simp; exists h
        apply m.nonzero
      . simp at h; exact h.1
    ⟩

instance [DecidableEq σ] : Coe (σ →₀ ℕ) (Monomial σ) where
  coe := fun m => ⟨
    m.support,
    fun x => m.toFun x.1,
    by
      rintro ⟨x,p⟩; simp
      apply (m.mem_support_toFun x).mp
      assumption
    ⟩

noncomputable instance [DecidableEq σ] [CommRing R] : Coe (Monomial σ) (MvPolynomial σ R) where
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
