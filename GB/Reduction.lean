-- import GB.CFinsupp
import GB.Monomial
import GB.Polynomial
import GB.S_Poly
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.CommRing


section Reduction
-- variable
-- [DecidableEq (Monomial σ )]

-- Reduction Procedure, aka multivariate divison algorithm

noncomputable def Monomial.div [DecidableEq σ] (f : Monomial σ) (g : Monomial σ) : (Monomial σ) × (Monomial σ) :=
  if (Monomial.instDvd' f g)
  then (f / g, 0)
  else (0, f)

def Generators (σ R: Type) [DecidableEq σ] [DecidableEq R] [CommRing R] : Type := Finset (MvPolynomial σ R)

instance Generators.instMembership (σ R: Type) [DecidableEq σ] [DecidableEq R] [CommRing R] : Membership (MvPolynomial σ R) (Generators σ R) where
  mem := Finset.instMembership.mem

noncomputable def MvPolynomial.divMonomial' [DecidableEq σ] [DecidableEq R] [Field R] (f : MvPolynomial σ R) (g : MvPolynomial σ R) (g_ismon : is_monomial g) : (MvPolynomial σ R) × (MvPolynomial σ R) :=
  (f.divMonomial (g.toMonomial g_ismon), f.modMonomial (g.toMonomial g_ismon))

def MvPolynomial.monomial_equiv [DecidableEq σ] [DecidableEq R] [Field R] (g : MvPolynomial σ R) (g_ismon : is_monomial g) : g = (monomial (g.toMonomial g_ismon)) 1 := by
  rw [toMonomial]
  ext m
  rw [coeff, coeff]
  rw [monomial, AddMonoidAlgebra.lsingle]
  rw [Finsupp.lsingle]; simp
  rw [DFunLike.coe, DFunLike.coe, Finsupp.instFunLike, LinearMap.instFunLike]; simp
  rw [LinearMap.instFunLike]; simp
  have ⟨_, PROP⟩ := g_ismon
  have ⟨m0, ⟨m0P1, m0P2⟩⟩ := is_monomial_fst g_ismon
  simp at m0P1
  have EQ4 : (Finset.choose (fun x ↦ True) g.support (is_monomial_fst g_ismon) = m0) := by
    have EQ5 := (@Finset.choose_mem _ (fun _ ↦ True) _ g.support (is_monomial_fst g_ismon))
    apply m0P2
    exact Finset.choose_spec (fun x ↦ True) g.support (is_monomial_fst g_ismon)
  rw [EQ4]
  rcases em (m ∈ g.support) with p | p
  . have EQ6 : m = m0 := by
      apply m0P2
      exact And.symm ⟨trivial, p⟩
    rw [<-EQ6]
    have EQ7 := (@Finsupp.single_eq_same _ _ _ m (@OfNat.ofNat R 1 One.toOfNat1))
    have EQ8 : g.toFun m = 1 := by
      apply PROP
      exact p
    rw [EQ8]
    symm
    exact EQ7
  . have EQ6 : g m = 0 := by
      have EQ7 := (Finsupp.mem_support_toFun g m)
      have EQ8 : ¬ (g m ≠ 0) := by
        intro H
        apply p
        exact mem_support_iff.mpr H
      exact Function.nmem_support.mp EQ8
    have NEQ : m0 ≠ m := by
      intro H
      apply m0P1
      rw [coeff]
      rw [H]
      exact EQ6
    have EQ7 := (@Finsupp.single_eq_of_ne _ _ _ m0 m (@OfNat.ofNat R 1 One.toOfNat1) NEQ)
    have EQ8 : g.toFun m = 0 := by
      exact EQ6
    rw [EQ8]
    exact id (Eq.symm EQ7)

-- def MvPolynomial.monomial_equiv' [DecidableEq σ] [DecidableEq R] [Field R] (g : MvPolynomial σ R) (g_ismon : is_monomial ) : g = (monomial g').toMonomial g_ismon := by
--   sorry

lemma MvPolynomial.divMonomial'_correct [DecidableEq σ] [ord : MonomialOrder σ] [DecidableEq R] [Field R] (f : MvPolynomial σ R) (g : MvPolynomial σ R) (g_ismon : is_monomial g):
  let (h,r) := f.divMonomial' g g_ismon;
  f = g*h+r ∧
  (r = 0 ∨ ∀m ∈ monomials r, ¬ Monomial.instDvd.dvd (@leading_monomial σ _ _ _ ord g (is_monomial_nonzero g_ismon)) m) := by
  constructor
  . have EQ := (MvPolynomial.divMonomial_add_modMonomial f (g.toMonomial g_ismon))
    have EQ2 : (g * f.divMonomial (g.toMonomial g_ismon) = (monomial (g.toMonomial g_ismon)) 1 * f.divMonomial (g.toMonomial g_ismon)) := by
      have EQ3 : g = (monomial (g.toMonomial g_ismon)) 1 := by
        apply monomial_equiv
      exact congrFun (congrArg HMul.hMul EQ3) (f.divMonomial (g.toMonomial g_ismon))
    exact
      Eq.symm
        (Mathlib.Tactic.Abel.subst_into_add (g * f.divMonomial (g.toMonomial g_ismon))
          (f.modMonomial (g.toMonomial g_ismon))
          ((monomial (g.toMonomial g_ismon)) 1 * f.divMonomial (g.toMonomial g_ismon))
          (f.modMonomial (g.toMonomial g_ismon)) f EQ2 rfl EQ)
  . rw [leading_monomial, monomials]
    rw [toMonomial]
    have ⟨m0, ⟨m0P1, m0P2⟩⟩ := is_monomial_fst g_ismon
    have EQ4 : (Finset.choose (fun x ↦ True) g.support (is_monomial_fst g_ismon) = m0) := by
      have EQ5 := (@Finset.choose_mem _ (fun _ ↦ True) _ g.support (is_monomial_fst g_ismon))
      apply m0P2
      exact Finset.choose_spec (fun x ↦ True) g.support (is_monomial_fst g_ismon)
    rw [EQ4]
    rcases em (f.modMonomial m0 = 0) with p | p
    . exact Or.symm (Or.inr p)
    . right
      intro m SUP DVD
      have LE : (m0 <= m) := by
        rw [Monomial.instDvd_equiv] at DVD
        rw [Monomial.instDvd_equiv'] at DVD
        rw [Monomial.instDvd''] at DVD
        unfold monomials at DVD
        have EQ5 : ((@Finset.max' (Monomial σ) MonomialOrder.toLinearOrder g.support (term_exists g (is_monomial_nonzero g_ismon))) = m0) := by
          apply m0P2
          constructor
          . exact (@Finset.max'_mem _ MonomialOrder.toLinearOrder g.support (term_exists g (is_monomial_nonzero g_ismon)))
          . exact trivial
        rw [<- EQ5]
        apply DVD
      have EQ5 := (@coeff_modMonomial_of_le _ _ _ _ _ f LE)
      have EQ6 := (Finsupp.mem_support_toFun (f.modMonomial m0) m).mp
      exact EQ6 SUP EQ5

-- Opaque
attribute [irreducible] MvPolynomial.divMonomial'


def thd [CommSemiring R] {σ n} (t : (Fin (n+1) → MvPolynomial σ R) × (MvPolynomial σ R) × (MvPolynomial σ R)) : (MvPolynomial σ R) :=
  let ⟨_, _, c⟩ := t
  c

def thrd [CommSemiring R] {σ n} (t : (Fin (n+1) → MvPolynomial σ R) × (MvPolynomial σ R) × (MvPolynomial σ R) × ℕ × Bool) : (MvPolynomial σ R) :=
  let ⟨_, _, c, _, _⟩ := t
  c
def frth [CommSemiring R] {σ n} (t : (Fin (n+1) → MvPolynomial σ R) × (MvPolynomial σ R) × (MvPolynomial σ R) × ℕ × Bool) : ℕ :=
  let ⟨_, _, _, c, _⟩ := t
  c
def ffth [CommSemiring R] {σ n} (t : (Fin (n+1) → MvPolynomial σ R) × (MvPolynomial σ R) × (MvPolynomial σ R) × ℕ × Bool) : Bool :=
  let ⟨_, _, _, _, c⟩ := t
  c

noncomputable def multidiv_subsubalgo [DecidableEq R] [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (n : ℕ)
  (f : MvPolynomial σ R) (fs : Fin (n+1) → MvPolynomial σ R) (fs_nonzero : ∀ m, fs m ≠ 0)
  (as : Fin (n+1) → MvPolynomial σ R) (r : MvPolynomial σ R) (p : MvPolynomial σ R) (i : ℕ) (NDO : Bool) :
  (Fin (n+1) → MvPolynomial σ R) × (MvPolynomial σ R) × (MvPolynomial σ R) × ℕ × Bool :=
  if p_nonzero : p ≠ 0
  then if (leading_monomial (fs i) (fs_nonzero i) ∣ leading_monomial p p_nonzero)
    then
      let as' : Fin (n+1) → MvPolynomial σ R := fun i => as i + toMvPolynomial (leading_monomial p p_nonzero / leading_monomial (fs i) (fs_nonzero i))
      let p' : MvPolynomial σ R := p - toMvPolynomial (leading_monomial p p_nonzero / leading_monomial (fs i) (fs_nonzero i)) * (fs i)
      ⟨as', r, p', i, false⟩
    else ⟨as, r, p, i+1, true⟩
  else ⟨as, r, p, i, false⟩

lemma multidiv_subsubalgo_lm [DecidableEq R] [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (n : ℕ)
  (f : MvPolynomial σ R) (fs : Fin (n+1) → MvPolynomial σ R) (fs_nonzero : ∀ m, fs m ≠ 0)
  (as : Fin (n+1) → MvPolynomial σ R) (r : MvPolynomial σ R) (p : MvPolynomial σ R) (i : ℕ) (NDO : Bool) :
  p = 0 ∨ p ≠ 0 ∧ (leading_monomial_opt (thrd (multidiv_subsubalgo n f fs fs_nonzero as r p i NDO)) < leading_monomial_opt p ∨ (ffth (multidiv_subsubalgo n f fs fs_nonzero as r p i NDO)) = true) := by
  rw [Classical.or_iff_not_imp_left]
  intro H
  unfold multidiv_subsubalgo
  rw [dif_pos H]
  constructor
  . apply H
  . rcases em (leading_monomial (fs ↑i) (multidiv_subsubalgo.proof_1 n fs fs_nonzero i) ∣ leading_monomial p H) with h | h
    . rw [if_pos h]
      unfold thrd ffth; simp
      unfold leading_monomial_opt
      rw [dif_pos H]
      rcases em (p - toMvPolynomial (leading_monomial p H / leading_monomial (fs ↑i) (multidiv_subsubalgo.proof_1 n fs fs_nonzero i)) * (fs i) ≠ 0) with h' | h'
      . rw [dif_pos h']
        unfold LT.lt instLTOption; simp
        unfold Option.lt; simp
        generalize EQ : leading_monomial (p - toMvPolynomial (leading_monomial p H / leading_monomial (fs ↑i) (multidiv_subsubalgo.proof_1 n fs fs_nonzero i)) * fs ↑i) h' = m
        symm at EQ
        have MEM : m ∈ (p - toMvPolynomial (leading_monomial p H / leading_monomial (fs ↑i) (multidiv_subsubalgo.proof_1 n fs fs_nonzero i)) * fs ↑i).support := by
          subst EQ
          apply leading_monomial_in
        have SP := Finsupp.mem_support_toFun (p - toMvPolynomial (leading_monomial p H / leading_monomial (fs ↑i) (multidiv_subsubalgo.proof_1 n fs fs_nonzero i)) * fs ↑i) m
        apply SP.mp at MEM
        have NEQ : p m - (toMvPolynomial (leading_monomial p H / leading_monomial (fs ↑i) (multidiv_subsubalgo.proof_1 n fs fs_nonzero i)) * fs ↑i).toFun m ≠ 0 := by
          have EQ'' : (p - toMvPolynomial (leading_monomial p H / leading_monomial (fs ↑i) (multidiv_subsubalgo.proof_1 n fs fs_nonzero i)) * fs ↑i).toFun m = p m - (toMvPolynomial (leading_monomial p H / leading_monomial (fs ↑i) (multidiv_subsubalgo.proof_1 n fs fs_nonzero i)) * fs ↑i).toFun m := by
            rfl
          rw [<-EQ'']
          assumption
        rw [<-not_le]
        intro LTEQ
        rw [le_iff_lt_or_eq] at LTEQ
        cases LTEQ with
        | inl LMLT =>
          apply NEQ
          sorry
        | inr LMEQ =>
          apply NEQ
          sorry
      . rw [dif_neg h']
        unfold LT.lt instLTOption; simp
        unfold Option.lt; simp
    . rw [if_neg h]
      unfold thrd ffth; simp

instance boolWellFounded : WellFounded Bool.linearOrder.lt := by
  unfold LT.lt Preorder.toLT PartialOrder.toPreorder LinearOrder.toPartialOrder Bool.linearOrder; simp
  unfold Bool.instLT; simp
  refine WellFounded.intro ?h
  intro a
  match a with
  | true =>
    apply Acc.intro
    intro b H
    simp at H
    subst H
    apply Acc.intro
    intro b H
    simp at H
  | false =>
    apply Acc.intro
    intro b H
    simp at H

instance boolWellFoundedRelation : WellFoundedRelation Bool where
  rel := Bool.linearOrder.lt
  wf := boolWellFounded

noncomputable def multidiv_subalgo_once [DecidableEq R] [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (n : ℕ)
  (f : MvPolynomial σ R) (fs : Fin (n+1) → MvPolynomial σ R) (fs_nonzero : ∀ m, fs m ≠ 0)
  (old_tuple : (Fin (n+1) → MvPolynomial σ R) × (MvPolynomial σ R) × (MvPolynomial σ R) × ℕ × Bool) :
  (Fin (n+1) → MvPolynomial σ R) × (MvPolynomial σ R) × (MvPolynomial σ R) :=
  let ⟨as, r, p, i, NDO⟩ := old_tuple
  if p_nonzero : p ≠ 0
  then if NDO_false : NDO = true then
    if i_LE : i <= n
      then multidiv_subalgo_once n f fs fs_nonzero (multidiv_subsubalgo n f fs fs_nonzero as r p i NDO)
      else ⟨as, r + leading_monomial p p_nonzero, p - leading_monomial p p_nonzero⟩
    else ⟨as, r, p⟩
  else ⟨as, r, p⟩
  termination_by (ffth old_tuple, n + 1 - frth old_tuple)
  decreasing_by
    rw [LT.lt, Preorder.toLT, PartialOrder.toPreorder, LinearOrder.toPartialOrder, Bool.linearOrder]; simp
    unfold Bool.instLT; simp
    apply Prod.lex_iff.mpr
    simp
    generalize EQ : multidiv_subsubalgo n f fs fs_nonzero as r p i NDO = otp
    cases otp with
    | mk as' otp' =>
      cases otp' with
      | mk r' otp'' =>
        cases otp'' with
        | mk p' otp''' =>
          cases otp''' with
          | mk i' NDO' =>
            unfold frth ffth; simp
            unfold multidiv_subsubalgo at EQ
            rw [dif_pos p_nonzero] at EQ
            simp at EQ
            rcases em (leading_monomial (fs ↑i) (multidiv_subsubalgo.proof_1 n fs fs_nonzero i) ∣ leading_monomial p p_nonzero) with h | h
            . rw [if_pos h] at EQ
              simp at EQ
              left
              constructor
              . obtain ⟨_, _, _, _, EQ5⟩ := EQ
                assumption
              . assumption
            . rw [if_neg h] at EQ
              simp at EQ
              right
              obtain ⟨_, _, _, EQ4, EQ5⟩ := EQ
              constructor
              . rw [NDO_false]
                assumption
              . rw [<-EQ4]
                simp
                have EQ' : n + 1 - i = n - i + 1 := by
                  exact Nat.sub_add_comm i_LE
                rw [EQ']
                exact lt_add_one (n - i)

noncomputable def multidiv_subalgo_once_wrap [DecidableEq R] [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (n : ℕ)
  (f : MvPolynomial σ R) (fs : Fin (n+1) → MvPolynomial σ R) (fs_nonzero : ∀ m, fs m ≠ 0)
  (as : Fin (n+1) → MvPolynomial σ R) (r : MvPolynomial σ R) (p : MvPolynomial σ R) :
  (Fin (n+1) → MvPolynomial σ R) × (MvPolynomial σ R) × (MvPolynomial σ R) :=
    multidiv_subalgo_once n f fs fs_nonzero ⟨as, r, p, 0, true⟩

noncomputable def multidiv_subalgo [DecidableEq R] [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (n : ℕ)
  (f : MvPolynomial σ R) (fs : Fin (n+1) → MvPolynomial σ R) (fs_nonzero : ∀ m, fs m ≠ 0)
  (old_tuple : (Fin (n+1) → MvPolynomial σ R) × (MvPolynomial σ R) × (MvPolynomial σ R)) :
  (Fin (n+1) → MvPolynomial σ R) × (MvPolynomial σ R) × (MvPolynomial σ R) :=
  let ⟨as, r, p⟩ := old_tuple
  if p_nonzero : p ≠ 0
  then multidiv_subalgo n f fs fs_nonzero (multidiv_subalgo_once_wrap n f fs fs_nonzero as r p)
  else ⟨as, r, p⟩
  termination_by (leading_monomial_opt (thd old_tuple))
  decreasing_by
    generalize EQ : multidiv_subalgo_once_wrap n f fs fs_nonzero as r p = otp
    cases otp with
    | mk as' otp' =>
      cases otp' with
      | mk r' p' =>
        unfold thd; simp
        unfold multidiv_subalgo_once_wrap at EQ
        -- unfold multidiv_subalgo_once at EQ
        sorry

noncomputable def multidiv_algo [DecidableEq R] [DecidableEq σ] [ord : MonomialOrder σ] [Field R] (n : ℕ)
  (f : MvPolynomial σ R) (fs : Fin (n+1) → MvPolynomial σ R) (fs_nonzero : ∀ m, fs m ≠ 0) :
  (Fin (n+1) → MvPolynomial σ R) × (MvPolynomial σ R) :=
  let ⟨as, r, _⟩ := multidiv_subalgo n f fs fs_nonzero ⟨fun _ => 0, 0, f⟩
  ⟨as, r⟩

noncomputable def MvPolynomial.multidiv [DecidableEq σ] [DecidableEq R] [LinearOrder σ] [Field R] [MonomialOrder σ]
  (s : MvPolynomial σ R) (F : Finset (MvPolynomial σ R)) (F_isNonzero : ∀ f ∈ F, f ≠ 0) :
    (Finsupp (MvPolynomial σ R) (MvPolynomial σ R)) × (MvPolynomial σ R) :=
  -- use multidiv_algo
  sorry

lemma MvPolynomial.multidiv_correct [DecidableEq R] [LinearOrder σ] [ord : MonomialOrder σ] [Field R]
  (s : MvPolynomial σ R) (F : Finset (MvPolynomial σ R)) (F_isNonzero : ∀ f ∈ F, f ≠ 0):
    s = (s.multidiv F F_isNonzero).snd + (∑ (f ∈ F), ((s.multidiv F F_isNonzero).fst f)*(f)) /\
    ((s.multidiv F F_isNonzero).snd = 0 ∨ ∀m ∈ monomials (s.multidiv F F_isNonzero).snd, ∀ f (inF : f ∈ F), ¬ Monomial.instDvd.dvd (leading_monomial f (F_isNonzero f inF)) m) := by
  sorry



-- noncomputable def MvPolynomial.div [DecidableEq σ] [DecidableEq R] [Field R] [MonomialOrder σ] (f : MvPolynomial σ R) (g : MvPolynomial σ R) (g_nonzero : g ≠ 0) : (MvPolynomial σ R) × (MvPolynomial σ R) :=
--   let glt := leading_monomial g g_nonzero
--   let h := f.divMonomial glt
--   (h, f - h*g)

-- lemma MvPolynomial.div_correct [DecidableEq σ] [DecidableEq R] [Field R] [ord : MonomialOrder σ] (f : MvPolynomial σ R) (g : MvPolynomial σ R) (g_nonzero : g ≠ 0):
--   let (h,r) := f.div g g_nonzero;
--   f = g*h+r ∧
--   (r = 0 ∨ ∀m ∈ monomials r, ¬ Monomial.instDvd.dvd (@leading_monomial σ _ _ _ ord g g_nonzero) m) := by
--   constructor
--   . have EQ : g * f.divMonomial (leading_monomial g g_nonzero) + (f - f.divMonomial (leading_monomial g g_nonzero) * g) = (g * f.divMonomial (leading_monomial g g_nonzero) + f) - f.divMonomial (leading_monomial g g_nonzero) * g := by
--       apply add_sub_assoc'
--     rw [EQ]
--     clear EQ
--     have EQ : g * f.divMonomial (leading_monomial g g_nonzero) + f - f.divMonomial (leading_monomial g g_nonzero) * g = f + g * f.divMonomial (leading_monomial g g_nonzero) - f.divMonomial (leading_monomial g g_nonzero) * g := by
--       have EQ' : g * f.divMonomial (leading_monomial g g_nonzero) + f = f + g * f.divMonomial (leading_monomial g g_nonzero) := by
--         apply add_comm
--       rw [EQ']
--     rw [EQ]
--     clear EQ
--     have EQ : g * f.divMonomial (leading_monomial g g_nonzero) = f.divMonomial (leading_monomial g g_nonzero) * g := by
--       apply mul_comm
--     rw [EQ]
--     clear EQ
--     symm
--     apply add_sub_cancel_right
--   . symm
--     apply or_iff_not_imp_right.mpr
--     intro H
--     have NEX : (¬ ∃ m ∈ monomials (f - f.divMonomial (leading_monomial g g_nonzero) * g), leading_monomial g g_nonzero ∣ m) := by
--       intro H'
--       obtain ⟨m, ⟨mP1, mP2⟩⟩ := H'
--       rw [Monomial.instDvd_equiv] at mP2
--       rw [Monomial.instDvd_equiv'] at mP2
--       rw [Monomial.instDvd''] at mP2

--       sorry
--     intro m H' X
--     apply NEX
--     use m
--     -- have gm : is_monomial ((monomial (leading_monomial g g_nonzero)) (1 : R)) := by
--     --   apply is_monomial_monomial
--     -- have EQ := (MvPolynomial.divMonomial'_correct f (leading_monomial g g_nonzero) gm)
--     -- unfold divMonomial' at EQ
--     -- simp at EQ
--     -- obtain ⟨EQ0, EQ1⟩ := EQ
--     -- sorry
--     -- have EQ' : f - f.divMonomial (leading_monomial g g_nonzero) * g = f.modMonomial (((monomial (leading_monomial g g_nonzero)) 1).toMonomial gm) := by
--     --   clear EQ1
--     --   have EQ2 : f = f.divMonomial (leading_monomial g g_nonzero) * g + f.modMonomial (((monomial (leading_monomial g g_nonzero)) 1).toMonomial gm) := by
--     --     have EQ3 : (monomial (leading_monomial g g_nonzero)) 1 * f.divMonomial (((monomial (leading_monomial g g_nonzero)) 1).toMonomial gm) = f.divMonomial (leading_monomial g g_nonzero) * g := by
--     --       sorry
--     --     rw [<-EQ3]
--     --     exact EQ0
--     --   clear EQ0
--     --   symm
--     --   apply eq_sub_of_add_eq'
--     --   symm
--     --   exact EQ2
--     -- rw [EQ']
--     -- clear EQ'
--     -- have EQ' : leading_monomial ((monomial (leading_monomial g g_nonzero)) 1) (is_monomial_nonzero gm) = leading_monomial g g_nonzero := by
--     --   clear EQ0 EQ1
--     --   apply monomial_leading_monomial
--     -- rw [EQ'] at EQ1
--     -- exact EQ1

-- noncomputable def MvPolynomial.multidiv_help [DecidableEq σ] [DecidableEq R] [LinearOrder σ] [Field R] [MonomialOrder σ] (s : MvPolynomial σ R) (F : List (MvPolynomial σ R)) (F_isNonzero : ∀ f ∈ F, f ≠ 0): (Finsupp (MvPolynomial σ R) (MvPolynomial σ R)) × (MvPolynomial σ R) :=
--   sorry
  -- match F with
  -- | [] => (0, s)
  -- | f :: F' =>
  --   let (h₁,r) := div s f (by simp at F_isNonzero; rcases F_isNonzero; assumption)
  --   let (h₂,r) := multidiv_help r F' (by intro f; simp at F_isNonzero; rcases F_isNonzero with ⟨_,h⟩ ; apply h)
  --   (h₂ + Finsupp.single f h₁, r)

-- lemma FList_isNonzero [CommRing R] {F : Finset (MvPolynomial σ R)} (F_isNonzero : ∀ f ∈ F, f ≠ 0) : ∀ f ∈ F.toList, f ≠ 0 := by
--   intro f fIn
--   rw [Finset.mem_toList] at fIn
--   apply F_isNonzero f fIn

-- noncomputable def MvPolynomial.multidiv [DecidableEq σ] [DecidableEq R] [LinearOrder σ]  [Field R] [MonomialOrder σ] (s : MvPolynomial σ R) (F : Finset (MvPolynomial σ R)) (F_isNonzero : ∀ f ∈ F, f ≠ 0) :
--     (Finsupp (MvPolynomial σ R) (MvPolynomial σ R)) × (MvPolynomial σ R) :=
--   sorry
  -- MvPolynomial.multidiv_help s (F.toList) (FList_isNonzero F_isNonzero)

-- lemma Finset.sumEQ [CommRing R] (s: Finset (MvPolynomial σ R)) (f: (MvPolynomial σ R) -> (MvPolynomial σ R)): s.sum f = (s.toList.map f).sum := by
--   unfold Finset.sum
--   rw [← Multiset.sum_toList]
--   have := Multiset.map_coe f s.toList
--   simp at this; rw [this]; clear this; simp

-- lemma MvPolynomial.multidiv_correct [DecidableEq R] [LinearOrder σ] [ord : MonomialOrder σ] [Field R] (s : MvPolynomial σ R) (F : Finset (MvPolynomial σ R)) (F_isNonzero : ∀ f ∈ F, f ≠ 0):
--     -- let (a,r) := (MvPolynomial.multidiv s F F_isNonzero);
--     s = (s.multidiv F F_isNonzero).snd + (∑ (f ∈ F), ((s.multidiv F F_isNonzero).fst f)*(f)) /\
--     ((s.multidiv F F_isNonzero).snd = 0 ∨ ∀m ∈ monomials (s.multidiv F F_isNonzero).snd, ∀ f (inF : f ∈ F), ¬ Monomial.instDvd.dvd (leading_monomial f (F_isNonzero f inF)) m) := by
--   sorry
  -- unfold multidiv; constructor
  -- . have : ∀ l (s : MvPolynomial σ R) F F_isNonzero (EQ: l = F.toList),
  --   s = (multidiv_help s l (by rw[EQ]; exact FList_isNonzero F_isNonzero)).2 + (∑ (f ∈ F), ((multidiv_help s l (by rw[EQ]; exact FList_isNonzero F_isNonzero)).1 f)*(f)) := by
  --     clear s F F_isNonzero
  --     intro l s F F_isNonzero EQ
  --     have F_isNonzero' := FList_isNonzero F_isNonzero
  --     rw [← EQ] at F_isNonzero'
  --     have EQ' : F = l.toFinset := by rw [EQ]; simp
  --     have G : ∀ l (s : MvPolynomial σ R) (l_isNonzero : ∀ f ∈ l, f ≠ 0), s = (s.multidiv_help l l_isNonzero).2 + (l.map (fun f => (s.multidiv_help l l_isNonzero).1 f * f)).sum := by
  --       intro l; induction' l with f F' IH
  --       <;> intro s l_isNonzero
  --       . unfold multidiv_help; simp
  --       . simp [multidiv_help]
  --         have IH' := IH (div s f (by apply l_isNonzero; apply List.mem_cons_self)).2 (by intros; apply l_isNonzero; apply List.mem_cons_of_mem; assumption)
  --         have div_correct := (MvPolynomial.div_correct s f (by apply l_isNonzero; apply List.mem_cons_self)).1
  --         nth_rewrite 1 [div_correct]
  --         nth_rewrite 1 [IH']
  --         -- rw [IH']
  --         sorry
  --     nth_rewrite 1 [G l s F_isNonzero'];
  --     rw [Finset.sumEQ]; congr!
  --   apply this; rfl; assumption
  -- . sorry
