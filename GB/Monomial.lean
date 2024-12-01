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

lemma LCM_idem (m : Monomial σ) : LCM m m = m := by
  unfold LCM
  rw [Finsupp.zipWith]
  rw [Finsupp.onFinset]; simp
  apply Finsupp.ext
  intro a
  simp

-- def LCM_computable [DecidableEq σ] : Computable₂ (@LCM σ) := by
--   sorry

noncomputable instance Monomial.instDiv [DecidableEq σ] : Div (Monomial σ) where
  div m1 m2 := Finsupp.zipWith (Nat.sub) (by rfl) m1 m2

lemma Monomial.div_same [DecidableEq σ] (m : Monomial σ) : m / m = 0 := by
  rw [Monomial.instDiv, HDiv.hDiv, instHDiv]; simp
  apply Finsupp.ext
  intro a
  simp

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

noncomputable def leading_monomial_opt [DecidableEq σ] [CommRing R] [DecidableEq R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) : Option (Monomial σ) :=
  if p_nonzero : p ≠ 0 then some (leading_monomial p p_nonzero) else none

lemma leading_monomial_in [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) :
  leading_monomial p p_nonzero ∈ p.support := by
  unfold leading_monomial
  unfold monomials
  apply Finset.max'_mem

lemma leading_monomial_nonzero [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) :
  MvPolynomial.coeff (leading_monomial p p_nonzero) p ≠ 0 := by
  have MEM := leading_monomial_in p p_nonzero
  apply (@Finsupp.mem_support_iff _ _ _ p (leading_monomial p p_nonzero)).mp at MEM
  apply MEM

lemma leading_monomial_sound [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0)
  (m : Monomial σ) (m_in : m ∈ p.support) :
  m ≤ leading_monomial p p_nonzero := by
  unfold leading_monomial
  unfold monomials
  apply Finset.le_max'
  assumption

lemma leading_monomial_smul_nonzero [DecidableEq σ] [Field R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0)
  (c : R) (NE : c ≠ 0) :
  c • p ≠ 0 := by
  apply smul_ne_zero <;> assumption

lemma leading_monomial_smul [DecidableEq σ] [Field R] [ord : MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0)
  (c : R) (NE : c ≠ 0) :
  leading_monomial (c • p) (leading_monomial_smul_nonzero p p_nonzero c NE) = leading_monomial p p_nonzero := by
  rw [leading_monomial, leading_monomial]
  unfold monomials
  have EQ := (MvPolynomial.support_smul_eq NE p)
  apply LE.le.antisymm'
  . apply Finset.max'_subset
    rw [EQ]
  . apply Finset.max'_subset
    rw [EQ]

def leading_coeff [DecidableEq σ] [CommRing R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) : R :=
  MvPolynomial.coeff (leading_monomial p p_nonzero) p

lemma leading_coeff_nonzero [DecidableEq σ] [CommRing R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) :
  leading_coeff p p_nonzero ≠ 0 := by
  unfold leading_coeff
  apply leading_monomial_nonzero

lemma leading_coeff_div_nonzero [DecidableEq σ] [Field R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) :
  (1 / leading_coeff p p_nonzero) • p ≠ 0 := by
  apply leading_monomial_smul_nonzero
  . assumption
  . apply one_div_ne_zero
    apply leading_coeff_nonzero

lemma leading_coeff_div [DecidableEq σ] [Field R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0) :
  leading_coeff ((1 / leading_coeff p p_nonzero) • p) (leading_coeff_div_nonzero p p_nonzero) = 1 := by
  nth_rewrite 1 [leading_coeff]
  rw [MvPolynomial.coeff_smul]
  rw [leading_monomial_smul p p_nonzero]
  . have EQ : MvPolynomial.coeff (leading_monomial p p_nonzero) p = leading_coeff p p_nonzero := by
      rfl
    rw [EQ]
    rw [HSMul.hSMul, instHSMul]; simp
    rw [SMul.smul, SMulZeroClass.toSMul, SMulWithZero.toSMulZeroClass, MulActionWithZero.toSMulWithZero]; simp
    rw [MulAction.toSMul, MulActionWithZero.toMulAction, Module.toMulActionWithZero]; simp
    unfold inferInstance
    rw [DistribMulAction.toMulAction, Module.toDistribMulAction, Algebra.toModule]; simp
    rw [Algebra.toSMul, Algebra.id]; simp
    rw [Mul.toSMul]; simp
    refine inv_mul_cancel₀ ?h
    exact leading_coeff_nonzero p p_nonzero
  . apply one_div_ne_zero
    apply leading_coeff_nonzero

lemma monomial_leading_monomial [DecidableEq σ] [Field R] [MonomialOrder σ ] (g : MvPolynomial σ R) (g_nonzero : g ≠ 0)
  (l_nonzero : (MvPolynomial.monomial (leading_monomial g g_nonzero)) (1 : R) ≠ 0) :
  leading_monomial ((MvPolynomial.monomial (leading_monomial g g_nonzero)) (1 : R)) l_nonzero = leading_monomial g g_nonzero := by
  let p := (MvPolynomial.monomial (leading_monomial g g_nonzero)) (1 : R)
  have EQ : leading_monomial p l_nonzero = leading_monomial g g_nonzero := by
    have EQ' : p = Finsupp.single (leading_monomial g g_nonzero) 1 := by
      rw [MvPolynomial.single_eq_monomial]
    rw [Finsupp.single] at EQ'; simp at EQ'
    have EQ'' : p.support = {leading_monomial g g_nonzero} := by
      rw [EQ']
      rfl
    have EQ''' := (leading_monomial_in p l_nonzero)
    rw [EQ''] at EQ'''
    rw [<-Set.mem_singleton_iff]
    exact Set.mem_toFinset.mp EQ'''
  unfold p at EQ
  exact EQ

instance opLinearOrder {T : Type} [LE : LinearOrder T] : LinearOrder (Option T) where
  le  p₁ p₂ := match p₁ with | none => True | some p1' => match p₂ with | none => False | some p2' => LE.le p1' p2'
  le_refl := by
    intro a
    simp
    cases a with
    | none => simp
    | some a' => simp
  le_trans := by
    simp
    intro a b c H1 H2
    cases a with
    | none => simp
    | some a' =>
      simp
      cases b with
      | none =>
        simp at H1
      | some b' =>
        cases c with
        | none =>
          simp at H2
        | some c' =>
          simp at H1 H2
          simp
          apply LE.le_trans <;> assumption
  le_antisymm := by
    simp
    intro a b H1 H2
    cases a with
    | none =>
      cases b with
      | none =>
        simp at H1 H2
        rfl
      | some b' =>
        simp at H1 H2
    | some a' =>
      cases b with
      | none =>
        simp at H1 H2
      | some b' =>
        simp at H1 H2
        have EQ : a' = b' := by
          apply LE.le_antisymm <;> assumption
        rw [EQ]
  le_total := by
    intro a b
    cases a with
    | none =>
      left
      simp
    | some a' =>
      cases b with
      | none =>
        right
        simp
      | some b' =>
        simp
        apply LE.le_total
  decidableLE := by
    intro a b
    simp
    cases a with
    | none =>
      simp
      exact instDecidableTrue
    | some a' =>
      cases b with
      | none =>
        simp
        exact instDecidableFalse
      | some b' =>
        simp
        apply LE.decidableLE
  lt_iff_le_not_le := by
    intro a b
    constructor <;> intro H
    . cases a with
      | none =>
        simp
        cases b with
        | none =>
          unfold LT.lt instLTOption at H; simp at H
          unfold Option.lt at H
          simp at H
        | some b' =>
          simp
      | some a' =>
        cases b with
        | none =>
          unfold LT.lt instLTOption at H; simp at H
          unfold Option.lt at H
          simp at H
        | some b' =>
          unfold LT.lt instLTOption at H; simp at H
          unfold Option.lt at H
          simp at H
          simp
          constructor
          . exact le_of_lt H
          . assumption
    . have ⟨H1, H2⟩ := H
      cases a with
      | none =>
        simp
        cases b with
        | none =>
          simp at H2
        | some b' =>
          unfold LT.lt instLTOption; simp
          unfold Option.lt
          simp
      | some a' =>
        cases b with
        | none =>
          simp at H1
        | some b' =>
          simp at H1 H2
          unfold LT.lt instLTOption; simp
          unfold Option.lt
          simp
          apply (LE.lt_iff_le_not_le a' b').mpr
          exact H
  min_def := by
    sorry
  max_def := by
    sorry
  compare_eq_compareOfLessAndEq := by
    sorry
