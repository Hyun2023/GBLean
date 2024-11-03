import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finset.Basic

section Monomial

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

instance ofMonomial [DecidableEq σ] : Coe (Monomial σ) (σ →₀ ℕ) where
  coe := fun m => ⟨
    m.support,
    fun x => if p: x ∈ m.support then m.toFun ⟨x,p⟩  else 0,
    by
      intro x; constructor <;> intro h
      . simp; exists h
        apply m.nonzero
      . simp at h; exact h.1
    ⟩

lemma funEq (f₁ f₂: A → B) :
    (f₁=f₂) -> ∀x, f₁ x = f₂ x := by
  intro EQ _; rw [EQ]

lemma Monomial_Funlike_injective [DecidableEq σ] : Function.Injective (fun m => ((@ofMonomial σ _).coe m).toFun) := by
    rintro ⟨A₁,p₁,nonzero₁⟩ ⟨A₂,p₂,nonzero₂⟩ h
    rw [Coe.coe, ofMonomial] at h; simp at h
    apply funEq at h
    have G1: A₁ = A₂ := by
      apply (@Finset.instIsAntisymmSubset σ).antisymm
      . intro x inA
        have h2 := h x; simp [inA] at h2
        rcases em (x∈A₂) with _|p; assumption
        simp [p] at h2
        exfalso; exact nonzero₁ ⟨x,inA⟩ h2
      . intro x inA
        have h2 := h x; simp [inA] at h2
        rcases em (x∈A₁) with _|p; assumption
        simp [p] at h2
        exfalso; apply nonzero₂ ⟨x,inA⟩; rw[h2]
    -- here "rw [G1] at p₁" gives p₁✝ at goal leaving p₁ at hyp
    -- which is just rejected tactic in coq (error: p₁ appears in the goal!)
    congr!
    -- congr! tactic leaves subgoal of Heq, which is almost impossible to solve.
    -- see https://proofassistants.stackexchange.com/questions/3856/lean4-how-to-construct-an-heq-between-dependent-functions
    -- can we use Equiv.cast to construct object of dependent sum type?
    have G2: Equiv.cast (by rw [G1]) p₁ = p₂ := by
      ext x; have h2 := h x
      rcases x with ⟨x,inA⟩; simp [inA] at h2
      rw [← G1] at inA; simp [inA] at h2
      rw [← h2]; simp; sorry
    sorry

instance toMonomial [DecidableEq σ] : Coe (σ →₀ ℕ) (Monomial σ) where
  coe := fun m => ⟨
    m.support,
    fun x => m.toFun x.1,
    by
      rintro ⟨x,p⟩; simp
      apply (m.mem_support_toFun x).mp
      assumption
    ⟩

lemma toMonomial_injective [DecidableEq σ] : Function.Injective (@toMonomial σ _).coe := by
  rintro ⟨A₁,p₁,nonzero₁⟩ ⟨A₂,p₂,nonzero₂⟩ h
  rw [Coe.coe, toMonomial] at h; simp at h
  rcases h with ⟨h1, h2⟩
  congr!; ext x
  sorry

def toMonomial_emb [DecidableEq σ] : (σ →₀ ℕ) ↪ (Monomial σ) where
  toFun := (@toMonomial σ _).coe
  inj' := toMonomial_injective

lemma toMonomial_ofMonomial_inverse [DecidableEq σ] : ∀ x, (@toMonomial σ _).coe (ofMonomial.coe x) = x := by
  intro x; rw [Coe.coe, Coe.coe, toMonomial, ofMonomial]; simp

lemma ofMonomial_toMonomial_inverse [DecidableEq σ] : ∀ x, (@ofMonomial σ _).coe (toMonomial.coe x) = x := by
  rintro ⟨A,p,h⟩ ; rw [Coe.coe, Coe.coe, toMonomial, ofMonomial]; simp
  ext x; have h' := h x
  rcases em (x ∈ A) with inA|inA <;> simp [inA]
  symm; by_contra!; rw [← h'] at this; contradiction

noncomputable instance [DecidableEq σ] [CommRing R] : Coe (Monomial σ) (MvPolynomial σ R) where
  coe := fun m => MvPolynomial.monomial m 1

instance Monomial.Funlike [DecidableEq σ] : FunLike (Monomial σ) σ ℕ where
  coe := fun m => ((@ofMonomial σ _).coe m).toFun
  coe_injective' := Monomial_Funlike_injective

-- almost same as Monomial.instMul. maybe defining general binary operation (and use it to define Monomial.instMul and LCM) might be better.
noncomputable def LCM [DecidableEq σ] (f g :Monomial σ) : (Monomial σ) where
  support := f.1 ∪ g.1
  toFun :=
    fun ⟨x, infg⟩ =>
      if pf: x∈f.1 then
        if pg: x∈g.1 then Nat.max (f.2 ⟨x, pf⟩) (g.2 ⟨x, pg⟩)
        else (f.2 ⟨x, pf⟩)
      else
        if pg: x∈g.1 then g.2 ⟨x, pg⟩
        else by
          have := Finset.union_contradiction pf pg
          contradiction
  nonzero := by
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


-- Monomial Order
class MonomialOrder (σ : Type) [DecidableEq σ] extends (LinearOrder (Monomial σ)) where
  respect : ∀(u v w : @Monomial σ),  u < v -> u*w < v*w
  isWellOrder : IsWellOrder (Monomial σ) (fun x y => x < y)

def monomials [DecidableEq σ] [CommRing R] (p : MvPolynomial σ R) : Finset (Monomial σ) :=
  Finset.map toMonomial_emb p.support


-- Leading Monomial and Term
def term_exists [DecidableEq σ] [CommRing R] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) : (monomials p).Nonempty := by
  have exM : exists m, MvPolynomial.coeff m p ≠ 0 := by
    rw [MvPolynomial.ne_zero_iff] at p_nonzero
    exact p_nonzero
  rcases exM with ⟨m, mcond⟩
  constructor; any_goals exact (toMonomial.coe m)
  rw [monomials, toMonomial_emb]
  apply Finset.mem_map.mpr; simp
  exists (m)

def leading_monomial [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): Monomial σ :=
  @Finset.max' _ ord.toLinearOrder (monomials p)
  (term_exists p p_nonzero)

-- If p is zero, it gives runtime error. Wait, runtime error in proof assistant?
def leading_monomial_unsafe [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) : (Monomial σ) :=
  @Option.get! _ MonomialExists (@Finset.max _ ord.toLinearOrder (monomials p))

def leading_coeff [DecidableEq σ] [CommRing R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0): R :=
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
