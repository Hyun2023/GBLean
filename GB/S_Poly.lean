import GB.Monomial
import GB.Polynomial
open Monomial

-- TODO
-- 1. Finish the definition of S-Polynomial.
-- 2. State and Prove some facts related to S Polynomial will be used in Buchberger or F4 alg


-- Definition of S-Polynomial
-- ((LCM (LM f) (LM g)) / (LT f)) * f - ((LCM (LM f) (LM g)) / (LT g)) * g
noncomputable def Spol_help [DecidableEq σ] [Field R] [ord : MonomialOrder σ ] (f g : MvPolynomial σ R) (f_NE : f ≠ 0) (g_NE : g ≠ 0) : MvPolynomial σ R :=
  (MvPolynomial.monomial ((LCM (leading_monomial f f_NE) (leading_monomial g g_NE)) / (leading_monomial f f_NE)) (Inv.inv (leading_coeff f f_NE)) * f) -
  (MvPolynomial.monomial ((LCM (leading_monomial f f_NE) (leading_monomial g g_NE)) / (leading_monomial g g_NE)) (Inv.inv (leading_coeff g g_NE)) * g)
noncomputable def Spol [DecidableEq σ] [Field R] [DecidableEq R] [ord : MonomialOrder σ ] (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  if f_NE : f = 0 then 0 else (if g_NE : g = 0 then 0 else Spol_help f g f_NE g_NE)
-- gives trivial value for zero polynomials

lemma func_sum_distr [DecidableEq σ] [DecidableEq R] [CommRing R]
  (f g : MvPolynomial σ R)
  (m : Monomial σ) :
  (f + g) m = f m + g m := by
  rfl

lemma func_sum_distr_gen [DecidableEq σ] [DecidableEq R] [CommRing R] {T : Type}
  (Fn : Finset T)
  (f : Fn -> MvPolynomial σ R)
  (m : Monomial σ) :
  (∑ n' : Fn, f n') m = ∑ n' : Fn, (f n') m := by
  rw [<-Finset.sum_to_list]
  rw [<-Finset.sum_to_list]
  rw [List.sum, List.sum]
  have EQ : ∀ l, (List.foldr (fun x1 x2 ↦ x1 + x2) 0 (List.map (fun n' ↦ f n') l)).toFun m =
      List.foldr (fun x1 x2 ↦ x1 + x2) 0 (List.map (fun n' ↦ (f n') m) l) := by
    intro l; induction' l with head tail IH <;> simp
    . rfl
    . rw [<-IH]
      apply func_sum_distr
  apply EQ

lemma func_sum_distr_gen_fin [DecidableEq σ] [DecidableEq R] [CommRing R] n
  (f : Fin n -> MvPolynomial σ R)
  (m : Monomial σ) :
  (∑ n' : Fin n, f n') m = ∑ n' : Fin n, (f n') m := by
  rw [<-Finset.sum_to_list]
  rw [<-Finset.sum_to_list]
  rw [List.sum, List.sum]
  have EQ : ∀ l, (List.foldr (fun x1 x2 ↦ x1 + x2) 0 (List.map (fun n' ↦ f n') l)).toFun m =
      List.foldr (fun x1 x2 ↦ x1 + x2) 0 (List.map (fun n' ↦ (f n') m) l) := by
    intro l; induction' l with head tail IH <;> simp
    . rfl
    . rw [<-IH]
      apply func_sum_distr
  apply EQ

lemma Spol_help_lemma5_help_help [DecidableEq σ] [DecidableEq R] [Field R] [ord : MonomialOrder σ ] n
  (c : Fin n -> R) (f : Fin n -> MvPolynomial σ R)
  (m : Monomial σ)
  (NE0 : ∀ (n' : Fin n), c n' ≠ 0)
  (NE1 : ∀ (n' : Fin n), f n' ≠ 0)
  (MDEG1 : ∀ (n' : Fin n), leading_monomial (f n') (NE1 n') = m)
  (NE2 : (∑ (n' : Fin n), (c n') • (f n')) ≠ 0)
  (MDEG2 : (leading_monomial (∑ (n' : Fin n), (c n') • (f n')) NE2) < m) :
  ∃ (c' : Fin n -> Fin n -> R),
  (∑ (n' : Fin n), (c n') • (f n')) = (∑ (n' : Fin n), ∑ (n'' : Fin n), (c' n' n'') • (Spol_help (f n') (f n'') (NE1 n') (NE1 n''))) := by
  let d := (fun n' => leading_coeff (f n') (NE1 n'))
  let lm := leading_monomial (∑ n' : Fin n, (c n') • f n') NE2
  have LT : lm < m := by
    exact MDEG2
  have EQ : (∑ (n' : Fin n), (c n') * (d n')) = 0 := by
    have EQ' : ¬ m ∈ (∑ n' : Fin n, (c n') • f n').support := by
      intro H
      have LE : m ≤ lm := by
        apply leading_monomial_sound
        assumption
      apply not_le.mpr at LT
      exact LT LE
    have EQ'' : (∑ n' : Fin n, (c n') • f n') m = 0 := by
      apply of_not_not
      intro H
      have MR := (Finsupp.mem_support_toFun (∑ n' : Fin n, c n' • f n') m)
      apply MR.mpr at H
      exact EQ' H
    rw [<- EQ'']
    clear EQ' EQ''
    rw [func_sum_distr_gen_fin]
    apply Finset.sum_congr; simp
    intro x H
    have EQ' := (MvPolynomial.coeff_smul m (c x) (f x))
    nth_rewrite 1 [MvPolynomial.coeff] at EQ'
    symm
    trans
    . apply EQ'
    . clear EQ'
      unfold d
      unfold leading_coeff
      rw [MDEG1 x]
      rfl
  let p := (fun n' => (1 / d n') • f n')
  have p_NE : (forall n', p n' ≠ 0) := by
    intro n'
    apply leading_coeff_div_nonzero
  have p_coeff_1 : forall n', leading_coeff (p n') (p_NE n') = 1 := by
    intro n'
    apply leading_coeff_div
  have EQ' : forall n', f n' = (d n') • (p n') := by
    intro n'
    unfold p
    unfold d
    have EQ'' : leading_coeff (f n') (NE1 n') • (1 / leading_coeff (f n') (NE1 n')) • f n' = (leading_coeff (f n') (NE1 n') * (1 / leading_coeff (f n') (NE1 n'))) • f n' := by
      apply smul_smul
    rw [EQ'']
    clear EQ''
    have EQ'' : leading_coeff (f n') (NE1 n') * (1 / leading_coeff (f n') (NE1 n')) = 1 := by
      refine mul_one_div_cancel ?h
      apply leading_coeff_nonzero
    rw [EQ'']
    exact Eq.symm (MulAction.one_smul (f n'))
  let S := (fun j k => Spol_help (f j) (f k) (NE1 j) (NE1 k))
  have S_EQ : ∀ j k, S j k = (p j) - (p k) := by
    intro j k
    unfold S
    rw [Spol_help]
    congr
    . rw [MDEG1 j]
      rw [MDEG1 k]
      rw [LCM_idem]
      rw [Monomial.div_same]
      unfold p
      rw [MvPolynomial.smul_eq_C_mul (f j)]
      unfold d
      rw [MvPolynomial.C_apply]
      simp
    . rw [MDEG1 j]
      rw [MDEG1 k]
      rw [LCM_idem]
      rw [Monomial.div_same]
      unfold p
      rw [MvPolynomial.smul_eq_C_mul (f k)]
      unfold d
      rw [MvPolynomial.C_apply]
      simp
  have NE0 : n ≠ 0 := by
    intro H
    apply NE2
    subst H
    simp
  have NE0' : ∃ n_p, n = n_p + 1 := by
    exact Nat.exists_eq_succ_of_ne_zero NE0
  clear NE0
  obtain ⟨n_p, nP⟩ := NE0'
  subst n
  have SMEQ : ∑ (n' : Fin (n_p + 1)), (c n') • f n' = ∑ (n' : Fin (n_p + 1)), (c n' * d n') • p n' := by
    apply Finset.sum_congr; simp
    intro x H
    rw [EQ']
    apply smul_smul
  have SMEQ' : ∑ (n' : Fin (n_p + 1)), (c n' * d n') • p n' = (∑ (n' : Fin n_p), (∑ (n'' : Fin (n' + 1)), c n'' * d n'') • ((p n') - (p (n' + 1)))) + (∑ (n'' : Fin (n_p + 1)), c n'' * d n'') • (p n_p) := by
    clear S S_EQ SMEQ
    have EQ'' : (∑ (n' : Fin n_p), (∑ (n'' : Fin (n' + 1)), c n'' * d n'') • ((p n') - (p (n' + 1)))) = (∑ (n' : Fin n_p), (((∑ (n'' : Fin (n' + 1)), c n'' * d n'') • (p n')) - ((∑ (n'' : Fin (n' + 1)), c n'' * d n'')) • (p (n' + 1)))) := by
      apply Finset.sum_congr; simp
      intro x H
      apply smul_sub
    rw [EQ'']
    clear EQ''
    have EQ'' : ∑ n' : Fin n_p,
        (((∑ n'' : Fin (↑n' + 1), c ↑↑n'' * d ↑↑n'') • p ↑↑n') -
        ((∑ n'' : Fin (↑n' + 1), c ↑↑n'' * d ↑↑n'') • p (↑↑n' + 1))) =
        (∑ n' : Fin n_p, (∑ n'' : Fin (↑n' + 1), c ↑↑n'' * d ↑↑n'') • p ↑↑n') -
        (∑ n' : Fin n_p, (∑ n'' : Fin (↑n' + 1), c ↑↑n'' * d ↑↑n'') • p (↑↑n' + 1)) := by
      exact Finset.sum_sub_distrib
    rw [EQ'']
    clear EQ''
    have EQ'' : ∑ n' : Fin (n_p + 1), (c n' * d n') • p n' = ∑ n' : Fin (n_p + 1), ((∑ n'' : Fin (↑n' + 1), c ↑↑n'' * d ↑↑n'') - (∑ n'' : Fin ↑n', c ↑↑n'' * d ↑↑n'')) • p n' := by
      apply Finset.sum_congr; simp
      intro x H
      have EQ''' : (c x * d x) = (∑ n'' : Fin (↑x + 1), c ↑↑n'' * d ↑↑n'' - ∑ n'' : Fin ↑x, c ↑↑n'' * d ↑↑n'') := by
        rw [Fin.sum_univ_castSucc]
        simp
      exact congrFun (congrArg HSMul.hSMul EQ''') (p x)
    rw [EQ'']
    clear EQ''
    have EQ'' : ∑ n' : Fin (n_p + 1), (∑ n'' : Fin (↑n' + 1), c ↑↑n'' * d ↑↑n'' - ∑ n'' : Fin ↑n', c ↑↑n'' * d ↑↑n'') • p n' =  ∑ n' : Fin (n_p + 1), ((∑ n'' : Fin (↑n' + 1), c ↑↑n'' * d ↑↑n'') • p n' - (∑ n'' : Fin ↑n', c ↑↑n'' * d ↑↑n'') • p n') := by
      apply Finset.sum_congr; simp
      intro x H
      exact
        sub_smul (∑ n'' : Fin (↑x + 1), c ↑↑n'' * d ↑↑n'') (∑ n'' : Fin ↑x, c ↑↑n'' * d ↑↑n'') (p x)
    rw [EQ'']
    clear EQ''
    have EQ'' : ∑ n' : Fin (n_p + 1),
      ((∑ n'' : Fin (↑n' + 1), c ↑↑n'' * d ↑↑n'') • p n' - (∑ n'' : Fin ↑n', c ↑↑n'' * d ↑↑n'') • p n') =
      (∑ n' : Fin (n_p + 1), (∑ n'' : Fin (↑n' + 1), c ↑↑n'' * d ↑↑n'') • p n') - (∑ n' : Fin (n_p + 1), (∑ n'' : Fin ↑n', c ↑↑n'' * d ↑↑n'') • p n') := by
      exact Finset.sum_sub_distrib
    rw [EQ'']
    clear EQ''
    have EQ'' : ∑ n' : Fin (n_p + 1), (∑ n'' : Fin (↑n' + 1), c ↑↑n'' * d ↑↑n'') • p n' = ∑ n' : Fin n_p, (∑ n'' : Fin (↑n' + 1), c ↑↑n'' * d ↑↑n'') • p ↑↑n' + (∑ n'' : Fin (n_p + 1), c n'' * d n'') • p ↑n_p := by
      rw [Fin.sum_univ_castSucc]
      simp
    rw [EQ'']
    clear EQ''
    have EQ'' : ∑ n' : Fin (n_p + 1), (∑ n'' : Fin ↑n', c ↑↑n'' * d ↑↑n'') • p n' = ∑ n' : Fin n_p, (∑ n'' : Fin (↑n' + 1), c ↑↑n'' * d ↑↑n'') • p (↑↑n' + 1) := by
      -- rw [Fin.sum_univ_castSucc]
      -- simp
      sorry
    rw [EQ'']
    clear EQ''
    apply add_sub_right_comm
  rw [SMEQ]
  clear SMEQ
  rw [SMEQ']
  clear SMEQ'
  rw [EQ]
  clear EQ
  rw [zero_smul]
  use (fun n' n'' => if n' < n_p ∧ n'' = n' + 1 then (∑ (k : Fin n''), (c k * d k)) else 0)
  simp
  rw [Fin.sum_univ_castSucc]
  simp
  apply Finset.sum_congr; simp
  intro x H
  have EQ : ∑ x_1 : Fin (n_p + 1),
      (if x.castSucc < Fin.last n_p ∧ x_1 = x.succ
      then (∑ k : Fin ↑x_1, c ↑↑k * d ↑↑k) • Spol_help (f x.castSucc) (f x_1) (NE1 x.castSucc) (NE1 x_1)
      else 0) =
    (∑ k : Fin ↑(x.succ), c ↑↑k * d ↑↑k) • Spol_help (f x.castSucc) (f x.succ) (NE1 x.castSucc) (NE1 x.succ) := by
    have EQ' : ∑ x_1 : Fin (n_p + 1),
      (if x.castSucc < Fin.last n_p ∧ x_1 = x.succ
      then (∑ k : Fin ↑x_1, c ↑↑k * d ↑↑k) • Spol_help (f x.castSucc) (f x_1) (NE1 x.castSucc) (NE1 x_1)
      else 0) =
      ∑ x_1 : Fin (n_p + 1),
      (if x_1 = x.succ
      then (∑ k : Fin ↑x_1, c ↑↑k * d ↑↑k) • Spol_help (f x.castSucc) (f x_1) (NE1 x.castSucc) (NE1 x_1)
      else 0) := by
      apply Finset.sum_congr; simp
      intro x' H'
      have LT : x.castSucc < Fin.last n_p := by
        rw [Fin.last, Fin.castSucc, Fin.castAdd, Fin.castLE]
        simp
      congr!
      apply Iff.symm
      exact iff_and_self.mpr fun a ↦ LT
    rw [EQ']
    clear EQ'
    simp
  rw [EQ]
  clear EQ
  simp
  specialize (S_EQ (x.castSucc) (x.succ))
  unfold S at S_EQ
  rw [S_EQ]

lemma Spol_help_lemma5_help [DecidableEq σ] [DecidableEq R] [Field R] [ord : MonomialOrder σ ] {T : Type}
  (Fn : Finset T)
  (c : Fn -> R) (f : Fn -> MvPolynomial σ R)
  (m : Monomial σ)
  (NE0 : ∀ (n' : Fn), c n' ≠ 0)
  (NE1 : ∀ (n' : Fn), f n' ≠ 0)
  (MDEG1 : ∀ (n' : Fn), leading_monomial (f n') (NE1 n') = m)
  (NE2 : (∑ (n' : Fn), (c n') • (f n')) ≠ 0)
  (MDEG2 : (leading_monomial (∑ (n' : Fn), (c n') • (f n')) NE2) < m) :
  ∃ (c_new : Fn -> Fn -> R),
  (∑ (n' : Fn), (c n') • (f n')) = (∑ (n' : Fn), ∑ (n'' : Fn), (c_new n' n'') • (Spol_help (f n') (f n'') (NE1 n') (NE1 n''))) := by
  have EQUIV := Equiv.symm (@Finset.equivFinOfCardEq _ Fn _ rfl)
  have BJ := Equiv.bijective EQUIV
  let NE0' : ∀ n', (c ∘ EQUIV.toFun) n' ≠ 0 := by
    intro n'
    apply NE0
  let NE1' : ∀ n', (f ∘ EQUIV.toFun) n' ≠ 0 := by
    intro n'
    apply NE1
  let MDEG1' : ∀ n', leading_monomial ((f ∘ EQUIV.toFun) n') (NE1' n') = m := by
    intro n'
    apply MDEG1
  let NE2' : (∑ (n' : Fin (Fn.card)), ((c ∘ EQUIV.toFun) n') • ((f ∘ EQUIV.toFun) n')) ≠ 0 := by
    have EQ' : ∑ n' : Fin Fn.card, (c ∘ EQUIV.toFun) n' • (f ∘ EQUIV.toFun) n' = ∑ n' : { x // x ∈ Fn }, c n' • f n' := by
      apply (@Function.Bijective.sum_comp _ _ _ _ _ _ _ BJ (fun n' => (c n') • (f n')))
    rw [EQ']
    apply NE2
  let MDEG2' : (leading_monomial (∑ (n' : Fin (Fn.card)), ((c ∘ EQUIV.toFun) n') • ((f ∘ EQUIV.toFun) n')) NE2') < m := by
    have EQ' : leading_monomial (∑ (n' : Fin (Fn.card)), ((c ∘ EQUIV.toFun) n') • ((f ∘ EQUIV.toFun) n')) NE2' = leading_monomial (∑ n' : { x // x ∈ Fn }, c n' • f n') NE2 := by
      have EQ2' := (@Function.Bijective.sum_comp _ _ _ _ _ _ _ BJ (fun n' => (c n') • (f n')))
      congr!
    rw [EQ']
    assumption
  have HLP := (Spol_help_lemma5_help_help Fn.card (c ∘ EQUIV.toFun) (f ∘ EQUIV.toFun) m NE0' NE1' MDEG1' NE2' MDEG2')
  obtain ⟨c', cPR⟩ := HLP
  let c'' : Fn -> Fn -> R := (fun n' n'' => c' (EQUIV.invFun n') (EQUIV.invFun n''))
  use c''
  have EQ1 : ∑ n' : { x // x ∈ Fn }, c n' • f n' = ∑ n' : Fin Fn.card, (c ∘ EQUIV.toFun) n' • (f ∘ EQUIV.toFun) n' := by
    symm
    apply (@Function.Bijective.sum_comp _ _ _ _ _ _ _ BJ (fun n' => (c n') • (f n')))
  have EQ2 : ∑ n' : { x // x ∈ Fn }, ∑ n'' : { x // x ∈ Fn }, c'' n' n'' • Spol_help (f n') (f n'') (NE1 n') (NE1 n'') = ∑ n' : Fin Fn.card, ∑ n'' : Fin Fn.card, c' n' n'' • Spol_help ((f ∘ EQUIV.toFun) n') ((f ∘ EQUIV.toFun) n'') (NE1' n') (NE1' n'') := by
    symm
    unfold c''
    have EQ'' : ∑ n' : Fin Fn.card, ∑ n'' : Fin Fn.card, c' n' n'' • Spol_help ((f ∘ EQUIV.toFun) n') ((f ∘ EQUIV.toFun) n'') (NE1' n') (NE1' n'') = ∑ n' : Fin Fn.card, ∑ n'' : Fin Fn.card, c' (EQUIV.invFun (EQUIV.toFun n')) (EQUIV.invFun (EQUIV.toFun n'')) • Spol_help ((f ∘ EQUIV.toFun) n') ((f ∘ EQUIV.toFun) n'') (NE1' n') (NE1' n'') := by
      apply Finset.sum_congr; simp
      intro x H
      apply Finset.sum_congr; simp
      intro x' H'
      simp
    rw [EQ'']
    clear EQ''
    have EQ2' := (@Function.Bijective.sum_comp _ _ _ _ _ _ _ BJ (fun n' => ∑ n'' : Fin Fn.card, c' (EQUIV.invFun n') (EQUIV.invFun (EQUIV.toFun n'')) • Spol_help (f n') ((f ∘ EQUIV.toFun) n'') (NE1 n') (NE1' n'')))
    trans
    . apply EQ2'
    . apply Finset.sum_congr; simp
      intro x H
      have EQ2'' := (@Function.Bijective.sum_comp _ _ _ _ _ _ _ BJ (fun n'' => c' (EQUIV.invFun x) (EQUIV.invFun n'') • Spol_help (f x) (f n'') (NE1 x) (NE1 n'')))
      apply EQ2''
  rw [EQ1]
  rw [EQ2]
  assumption

lemma Spol_help_lemma5 [DecidableEq σ] [DecidableEq R] [Field R] [ord : MonomialOrder σ ] {T : Type}
  (Fn : Finset T)
  (c : Fn -> R) (f : Fn -> MvPolynomial σ R)
  (m : Monomial σ)
  (NE1 : ∀ (n' : Fn), f n' ≠ 0)
  (MDEG1 : ∀ (n' : Fn), leading_monomial (f n') (NE1 n') = m)
  (NE2 : (∑ (n' : Fn), (c n') • (f n')) ≠ 0)
  (MDEG2 : (leading_monomial (∑ (n' : Fn), (c n') • (f n')) NE2) < m) :
  ∃ (c_new : Fn -> Fn -> R),
  (∑ (n' : Fn), (c n') • (f n')) = (∑ (n' : Fn), ∑ (n'' : Fn), (c_new n' n'') • (Spol_help (f n') (f n'') (NE1 n') (NE1 n''))) := by
  let Fn' : Finset Fn := Finset.filter (fun x ↦ ¬c x = 0) Fn.attach
  let c' : Fn' -> R := fun n => c n
  let f' : Fn' -> MvPolynomial σ R := fun n => f n
  let NE0' : ∀ (n' : Fn'), c n' ≠ 0 := by
    intro n'
    have Pf := (n'.2)
    unfold Fn' at Pf
    rw [Finset.mem_filter] at Pf
    have ⟨Pf1, Pf2⟩ := Pf
    exact Pf2
  let NE1' : ∀ (n' : Fn'), f' n' ≠ 0 := fun n' => NE1 n'
  let MDEG1' : ∀ (n' : Fn'), leading_monomial (f' n') (NE1' n') = m := fun n' => MDEG1 n'
  have Lem := Spol_help_lemma5_help Fn' c' f' m NE0' NE1'
  have EQ0 : (∑ (n' : Fn), (c n') • (f n')) = (∑ x ∈ Finset.filter (fun x ↦ True) Fn.attach, (c x) • f x) := by
    simp
  have EQ : (∑ (n' : Fn'), (c' n') • (f' n')) = (∑ (n' : Fn), (c n') • (f n')) := by
    rw [EQ0]
    have EQ1 := (Finset.sum_filter_add_sum_filter_not (Finset.filter (fun x ↦ True) Fn.attach) (fun n' : Fn => c n' = 0) (fun n' => (c n') • (f n')))
    rw [<- EQ1]
    have EQ2 : ∑ x ∈ Finset.filter (fun x ↦ c x = 0) (Finset.filter (fun x ↦ True) Fn.attach), (c x) • f x = 0 := by
      apply Finset.sum_eq_zero
      intro x
      simp
      intro H; rw [H]
      left
      simp
    rw [EQ2]
    have EQ3 : ∑ n' : { x // x ∈ Fn' }, (c' n') • f' n' = ∑ x ∈ Finset.filter (fun x ↦ ¬c x = 0) (Finset.filter (fun n' ↦ True) Fn.attach), (c x) • f x := by
      unfold Fn'; simp
      unfold c'; unfold f'
      have EQ4 := (@Finset.sum_finset_coe Fn _ _ (fun n' => (c n') • f n') (Finset.filter (fun x ↦ ¬c x = 0) Fn.attach))
      have EQ5 : (∑ i : ↑↑(Finset.filter (fun x ↦ ¬c x = 0) Fn.attach), (c ↑i) • f ↑i) = (∑ n' ∈ (Finset.filter (fun x ↦ ¬c x = 0) Fn.attach).attach, (c ↑n') • f ↑n') := by
        simp
      rw [<-EQ5]
      rw [<-EQ4]
      simp
    rw [EQ3]
    symm
    apply AddZeroClass.zero_add
  clear EQ0
  have MDEG1' : ∀ (n' : Fn'), leading_monomial (f' n') (NE1' n') = m := by
    intro n'
    apply MDEG1
  have NE2' : (∑ (n' : Fn'), (c' n') • (f' n')) ≠ 0 := by
    rw [EQ]
    apply NE2
  have MDEG2' : (leading_monomial (∑ (n' : Fn'), (c' n') • (f' n')) NE2') < m := by
    have EQ1 : leading_monomial (∑ n' : { x // x ∈ Fn }, (c n') • f n') NE2 = leading_monomial (∑ (n' : Fn'), (c' n') • (f' n')) NE2' := by
      congr!
      rw [EQ]
    rw [<- EQ1]
    apply MDEG2
  specialize (Lem MDEG1' NE2' MDEG2')
  have ⟨c_new', CP⟩ := Lem
  have DEC : ∀ n', Decidable (n' ∈ Fn') := by
    intro n'
    unfold Fn'
    simp
    apply instDecidableNot
  let c_new : Fn -> Fn -> R :=
    fun n m => if NEQ1 : n ∈ Fn' then (if NEQ2 : m ∈ Fn' then (c_new' ⟨n, NEQ1⟩ ⟨m, NEQ2⟩) else 0) else 0
  exists c_new
  unfold c_new
  clear Lem NE2' MDEG2'
  rw [EQ] at CP
  rw [CP]
  have EQ0 : (∑ (n' : Fn),
        ∑ n'' : { x // x ∈ Fn },
          (if NEQ1 : n' ∈ Fn' then if NEQ2 : n'' ∈ Fn' then c_new' ⟨n', NEQ1⟩ ⟨n'', NEQ2⟩ else 0 else 0) •
            Spol_help (f n') (f n'') (NE1 n') (NE1 n'')) =
      (∑ n' ∈ Finset.filter (fun x ↦ True) Fn.attach,
        ∑ n'' ∈ Finset.filter (fun x ↦ True) Fn.attach,
          (if NEQ1 : n' ∈ Fn' then if NEQ2 : n'' ∈ Fn' then c_new' ⟨n', NEQ1⟩ ⟨n'', NEQ2⟩ else 0 else 0) •
            Spol_help (f n') (f n'') (NE1 n') (NE1 n'')) := by
    simp
  rw [EQ0]
  clear EQ0
  have EQ1 := (Finset.sum_filter_add_sum_filter_not (Finset.filter (fun x ↦ True) Fn.attach)
    (fun n' : Fn => c n' = 0)
    (fun n' => ∑ n'' ∈ Finset.filter (fun x ↦ True) Fn.attach,
          (if NEQ1 : n' ∈ Fn' then if NEQ2 : n'' ∈ Fn' then c_new' ⟨n', NEQ1⟩ ⟨n'', NEQ2⟩ else 0 else 0) •
            Spol_help (f n') (f n'') (NE1 n') (NE1 n'')))
  rw [<- EQ1]
  clear EQ1
  have EQ2 : (∑ x ∈ Finset.filter (fun x ↦ c x = 0) (Finset.filter (fun x ↦ True) Fn.attach),
      ∑ n'' ∈ Finset.filter (fun x ↦ True) Fn.attach,
        (if NEQ1 : x ∈ Fn' then if NEQ2 : n'' ∈ Fn' then c_new' ⟨x, NEQ1⟩ ⟨n'', NEQ2⟩ else 0 else 0) •
          Spol_help (f x) (f n'') (NE1 x) (NE1 n'') = 0) := by
    apply Finset.sum_eq_zero
    intro x
    simp
    intro H
    have MEM : ¬ x ∈ Fn' := by
      unfold Fn'
      simp
      apply H
    intro h
    exfalso; apply MEM; assumption
  rw [EQ2]
  clear EQ2
  rw [AddZeroClass.zero_add]
  have EQ1 : (∑ x ∈ Finset.filter (fun x ↦ ¬c x = 0) (Finset.filter (fun x ↦ True) Fn.attach),
        ∑ n'' ∈ Finset.filter (fun x ↦ True) Fn.attach,
          (if NEQ1 : x ∈ Fn' then if NEQ2 : n'' ∈ Fn' then c_new' ⟨x, NEQ1⟩ ⟨n'', NEQ2⟩ else 0 else 0) •
            Spol_help (f x) (f n'') (NE1 x) (NE1 n'')) =
      (∑ x ∈ Finset.filter (fun x ↦ ¬c x = 0) (Finset.filter (fun x ↦ True) Fn.attach),
        ∑ n'' ∈ Finset.filter (fun x ↦ ¬c x = 0) (Finset.filter (fun x ↦ True) Fn.attach),
          (c_new x n'') •
            Spol_help (f x) (f n'') (NE1 x) (NE1 n'')) := by
    apply Finset.sum_congr; simp
    intro x H
    have EQ2 := (Finset.sum_filter_add_sum_filter_not (Finset.filter (fun x ↦ True) Fn.attach)
      (fun n' : Fn => c n' = 0)
      (fun n'' => (if NEQ1 : x ∈ Fn' then if NEQ2 : n'' ∈ Fn' then c_new' ⟨x, NEQ1⟩ ⟨n'', NEQ2⟩ else 0 else 0) •
            Spol_help (f x) (f n'') (NE1 x) (NE1 n'')))
    rw [<- EQ2]
    clear EQ2
    have EQ3 : (∑ x_1 ∈ Finset.filter (fun x ↦ c x = 0) (Finset.filter (fun x ↦ True) Fn.attach),
      (if NEQ1 : x ∈ Fn' then if NEQ2 : x_1 ∈ Fn' then c_new' ⟨x, NEQ1⟩ ⟨x_1, NEQ2⟩ else 0 else 0) •
        Spol_help (f x) (f x_1) (NE1 x) (NE1 x_1)) = 0 := by
      apply Finset.sum_eq_zero
      intro x' H'
      have MEM : x ∈ Fn' := by
        unfold Fn'
        simp
        rw [Finset.mem_filter] at H
        have ⟨_, H''⟩ := H
        exact H''
      rw [@dif_pos (x ∈ Fn') (DEC x) MEM]
      have MEM2 : ¬ x' ∈ Fn' := by
        unfold Fn'
        simp
        rw [Finset.mem_filter] at H'
        have ⟨_, H''⟩ := H'
        exact H''
      rw [@dif_neg (x' ∈ Fn') (DEC x') MEM2]
      apply zero_smul
    rw [EQ3]
    clear EQ3
    rw [AddZeroClass.zero_add]
  rw [EQ1]
  clear EQ1
  rw [Finset.filter_filter]
  have EQ1 : ∑ n' : { x // x ∈ Fn' }, ∑ n'' : { x // x ∈ Fn' }, (c_new' n' n'') • Spol_help (f' n') (f' n'') (NE1' n') (NE1' n'') =
    ∑ n' : { x // x ∈ Fn' }, ∑ n'' : { x // x ∈ Fn' }, (c_new n' n'') • Spol_help (f n') (f n'') (NE1 n') (NE1 n'') := by
    unfold f'
    unfold NE1'
    unfold c_new
    apply Finset.sum_congr; simp
    intro x H
    apply Finset.sum_congr; simp
    intro x_1 H_1
    simp
  rw [EQ1]
  clear EQ1
  have EQ4 := (@Finset.sum_finset_coe Fn _ _ (fun n' => ∑ n'' : { x // x ∈ Fn' }, (c_new n' ↑n'') • Spol_help (f n') (f ↑n'') (NE1 n') (NE1 ↑n'')) (Finset.filter (fun x ↦ ¬c x = 0) Fn.attach))
  have EQ5 : (∑ i : ↑↑(Finset.filter (fun x ↦ ¬c x = 0) Fn.attach),
      ∑ n'' : { x // x ∈ Fn' }, (c_new ↑i ↑n'') • Spol_help (f ↑i) (f ↑n'') (NE1 ↑i) (NE1 ↑n'')) =
      (∑ n' : { x // x ∈ Fn' }, ∑ n'' : { x // x ∈ Fn' }, (c_new ↑n' ↑n'') • Spol_help (f ↑n') (f ↑n'') (NE1 ↑n') (NE1 ↑n'')) := by
    simp
  rewrite [<-EQ5]
  clear EQ5
  have EQ6 : (∑ i ∈ Finset.filter (fun x ↦ ¬c x = 0) Fn.attach,
    ∑ n'' : { x // x ∈ Fn' }, (c_new i ↑n'') • Spol_help (f i) (f ↑n'') (NE1 i) (NE1 ↑n'')) =
    (∑ x ∈ Finset.filter (fun a ↦ True ∧ ¬c a = 0) Fn.attach,
      ∑ n'' ∈ Finset.filter (fun a ↦ True ∧ ¬c a = 0) Fn.attach,
        (c_new x n'') • Spol_help (f x) (f n'') (NE1 x) (NE1 n'')) := by
    clear EQ4
    simp
    apply Finset.sum_congr; simp
    intro x H
    have EQ4 := (@Finset.sum_finset_coe Fn _ _ (fun n'' => (c_new x n'') • Spol_help (f x) (f ↑n'') (NE1 x) (NE1 ↑n'')) (Finset.filter (fun x ↦ ¬c x = 0) Fn.attach))
    have EQ5 : (∑ i : ↑↑(Finset.filter (fun x ↦ ¬c x = 0) Fn.attach), (c_new x ↑i) • Spol_help (f x) (f ↑i) (NE1 x) (NE1 ↑i)) =
      (∑ n'' ∈ Fn'.attach, (c_new x ↑n'') • Spol_help (f x) (f ↑n'') (NE1 x) (NE1 ↑n'')) := by
      simp
    rewrite [<-EQ5]
    clear EQ5
    rw [<-EQ4]
    simp
  rw [<-EQ6]
  apply EQ4




-- lemma func_sum_distr_gen [DecidableEq σ] [DecidableEq R] [CommRing R] {T : Type}
--   (Fn : Finset T)
--   (f : Fn -> MvPolynomial σ R)
--   (m : Monomial σ) :
--   (∑ n' : Fn, f n') m = ∑ n' : Fn, (f n') m := by
--   have EQUIV := Equiv.symm (@Finset.equivFinOfCardEq _ Fn _ rfl)
--   have BJ := Equiv.bijective EQUIV
--   have FIN := (func_sum_distr_gen_fin Fn.card (f ∘ EQUIV.toFun) m)
--   have EQ1 : (∑ n' : { x // x ∈ Fn }, f n') m = (∑ n' : Fin Fn.card, (f ∘ EQUIV.toFun) n') m := by
--     clear FIN
--     have EQ1' := (@Function.Bijective.sum_comp _ _ _ _ _ _ _ BJ (fun n' => f n' m))
--     sorry
--   have EQ2 : ∑ n' : { x // x ∈ Fn }, (f n') m = ∑ n' : Fin Fn.card, ((f ∘ EQUIV.toFun) n') m := by
--     clear FIN
--     have EQ2' := (@Function.Bijective.sum_comp _ _ _ _ _ _ _ BJ (fun n' => f n' m))
--     sorry
--   rw [EQ1]
--   rw [EQ2]
--   exact FIN


-- lemma Spol_help_lemma5 [DecidableEq σ] [DecidableEq R] [Field R] [ord : MonomialOrder σ ] n (c : Fin n -> R) (f : Fin n -> MvPolynomial σ R)
--   (m : Monomial σ)
--   (NE1 : ∀ (n' : Fin n), f n' ≠ 0)
--   (MDEG1 : ∀ (n' : Fin n), leading_monomial (f n') (NE1 n') = m)
--   (NE2 : (∑ (n' : Fin n), (MvPolynomial.C (c n')) * (f n')) ≠ 0)
--   (MDEG2 : (leading_monomial (∑ (n' : Fin n), (MvPolynomial.C (c n')) * (f n')) NE2) < m) :
--   ∃ (c' : Fin n -> Fin n -> R),
--   (∑ (n' : Fin n), (MvPolynomial.C (c n')) * (f n')) = (∑ (n' : Fin n), ∑ (n'' : Fin n), (MvPolynomial.C (c' n' n'')) * (Spol_help (f n') (f n'') (NE1 n') (NE1 n''))) := by
--   let NZ : Finset (Fin n) := { n' | c n' ≠ 0 }
--   let crd : ℕ := NZ.card
--   have EQ : Multiset.card (Fin crd) = crd by
--     sorry
--   let d := (fun n' => leading_coeff (f n') (NE1 n'))
--   -- induction' n with np IH; simp
--   -- simp
--   sorry
