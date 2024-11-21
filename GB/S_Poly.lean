import GB.Monomial
import GB.Polynomial
open Monomial

-- TODO
-- 1. Finish the definition of S-Polynomial.
-- 2. State and Prove some facts related to S Polynomial will be used in Buchberger or F4 alg


-- Definition of S-Polynomial
-- ((LCM (LM f) (LM g)) / (LT f)) * f - ((LCM (LM f) (LM g)) / (LT g)) * g
noncomputable def Spol_help [DecidableEq σ] [Field R] [ord : MonomialOrder σ ] (f g : MvPolynomial σ R) (f_NE : f ≠ 0) (g_NE : g ≠ 0) : MvPolynomial σ R :=
  MvPolynomial.instSub.sub
    (MvPolynomial.monomial ((LCM (leading_monomial f f_NE) (leading_monomial g g_NE)) / (leading_monomial f f_NE)) (Inv.inv (leading_coeff f f_NE)) * f)
    (MvPolynomial.monomial ((LCM (leading_monomial f f_NE) (leading_monomial g g_NE)) / (leading_monomial g g_NE)) (Inv.inv (leading_coeff g g_NE)) * g)
noncomputable def Spol [DecidableEq σ] [Field R] [DecidableEq R] [ord : MonomialOrder σ ] (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  if f_NE : f = 0 then 0 else (if g_NE : g = 0 then 0 else Spol_help f g f_NE g_NE)
-- gives trivial value for zero polynomials

lemma func_sum_distr [DecidableEq σ] [DecidableEq R] [Field R] [ord : MonomialOrder σ ]
  (f g : MvPolynomial σ R)
  (m : Monomial σ) :
  (f + g) m = f m + g m := by
  rfl

lemma func_sum_distr_gen [DecidableEq σ] [DecidableEq R] [Field R] [ord : MonomialOrder σ ] {T : Type}
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

lemma Spol_help_lemma5_help [DecidableEq σ] [DecidableEq R] [Field R] [ord : MonomialOrder σ ] {T : Type}
  (Fn : Finset T)
  (c : Fn -> R) (f : Fn -> MvPolynomial σ R)
  (m : Monomial σ)
  (NE0 : ∀ (n' : Fn), c n' ≠ 0)
  (NE1 : ∀ (n' : Fn), f n' ≠ 0)
  (MDEG1 : ∀ (n' : Fn), leading_monomial (f n') (NE1 n') = m)
  (NE2 : (∑ (n' : Fn), (MvPolynomial.C (c n')) * (f n')) ≠ 0)
  (MDEG2 : (leading_monomial (∑ (n' : Fn), (MvPolynomial.C (c n')) * (f n')) NE2) < m) :
  ∃ (c_new : Fn -> Fn -> R),
  (∑ (n' : Fn), (MvPolynomial.C (c n')) * (f n')) = (∑ (n' : Fn), ∑ (n'' : Fn), (MvPolynomial.C (c_new n' n'')) * (Spol_help (f n') (f n'') (NE1 n') (NE1 n''))) := by
  let d := (fun n' => leading_coeff (f n') (NE1 n'))
  let p := leading_monomial (∑ n' : { x // x ∈ Fn }, MvPolynomial.C (c n') * f n') NE2
  -- have LE : p ≤ m := by
  --   have MEM : p ∈ (∑ n' : { x // x ∈ Fn }, MvPolynomial.C (c n') * f n').support := by
  --     apply leading_monomial_in
  --   have NE : (∑ n' : { x // x ∈ Fn }, MvPolynomial.C (c n') * f n').toFun p ≠ 0 := by
  --     rw [<-Finsupp.mem_support_toFun]
  --     assumption
  --   rw [<- not_lt]
  --   intro H
  --   apply NE
  --   have EQ' : (∑ n' : Fn, MvPolynomial.C (c n') * f n').toFun p = ∑ n' : Fn, (MvPolynomial.C (c n') * f n').toFun p := by
  --     sorry
  --   rw [EQ']
  --   clear EQ'
  --   apply Finset.sum_eq_zero
  --   intro x H'
  --   have EQ' : (MvPolynomial.C (c x) * (f x)).toFun p = (c x) * ((f x) p) := by
  --     sorry
  --   rw [EQ']
  --   clear EQ'
  --   simp; right
  --   have NN : (¬ (f x) p ≠ 0) := by
  --     intro H''
  --     have EQ'' : (f x).toFun p ≠ 0 := by
  --       apply H''
  --     rw [<-Finsupp.mem_support_toFun (f x) p] at EQ''
  --     have LE' : p ≤ m := by
  --       rw [<- MDEG1 x]
  --       apply leading_monomial_sound
  --       assumption
  --     rw [<-not_lt] at LE'
  --     apply LE'
  --     assumption
  --   exact Function.nmem_support.mp NN
  have LT : p < m := by
    exact MDEG2
  have EQ : (∑ (n' : Fn), (c n') * (d n')) = 0 := by
    have EQ' : ¬ m ∈ (∑ n' : Fn, MvPolynomial.C (c n') * f n').support := by
      intro H
      apply (Finsupp.mem_support_toFun (∑ n' : { x // x ∈ Fn }, MvPolynomial.C (c n') * f n') m).mp at H
      apply H
      sorry
    sorry
  sorry

lemma Spol_help_lemma5 [DecidableEq σ] [DecidableEq R] [Field R] [ord : MonomialOrder σ ] {T : Type}
  (Fn : Finset T)
  (c : Fn -> R) (f : Fn -> MvPolynomial σ R)
  (m : Monomial σ)
  (NE1 : ∀ (n' : Fn), f n' ≠ 0)
  (MDEG1 : ∀ (n' : Fn), leading_monomial (f n') (NE1 n') = m)
  (NE2 : (∑ (n' : Fn), (MvPolynomial.C (c n')) * (f n')) ≠ 0)
  (MDEG2 : (leading_monomial (∑ (n' : Fn), (MvPolynomial.C (c n')) * (f n')) NE2) < m) :
  ∃ (c_new : Fn -> Fn -> R),
  (∑ (n' : Fn), (MvPolynomial.C (c n')) * (f n')) = (∑ (n' : Fn), ∑ (n'' : Fn), (MvPolynomial.C (c_new n' n'')) * (Spol_help (f n') (f n'') (NE1 n') (NE1 n''))) := by
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
  have EQ0 : (∑ (n' : Fn), (MvPolynomial.C (c n')) * (f n')) = (∑ x ∈ Finset.filter (fun x ↦ True) Fn.attach, MvPolynomial.C (c x) * f x) := by
    simp
  have EQ : (∑ (n' : Fn'), (MvPolynomial.C (c' n')) * (f' n')) = (∑ (n' : Fn), (MvPolynomial.C (c n')) * (f n')) := by
    rw [EQ0]
    have EQ1 := (Finset.sum_filter_add_sum_filter_not (Finset.filter (fun x ↦ True) Fn.attach) (fun n' : Fn => c n' = 0) (fun n' => (MvPolynomial.C (c n')) * (f n')))
    rw [<- EQ1]
    have EQ2 : ∑ x ∈ Finset.filter (fun x ↦ c x = 0) (Finset.filter (fun x ↦ True) Fn.attach), MvPolynomial.C (c x) * f x = 0 := by
      apply Finset.sum_eq_zero
      intro x
      simp
      intro H; rw [H]
      rw [MvPolynomial.C_0]
      exact zero_mul (f x)
    rw [EQ2]
    have EQ3 : ∑ n' : { x // x ∈ Fn' }, MvPolynomial.C (c' n') * f' n' = ∑ x ∈ Finset.filter (fun x ↦ ¬c x = 0) (Finset.filter (fun n' ↦ True) Fn.attach), MvPolynomial.C (c x) * f x := by
      unfold Fn'; simp
      unfold c'; unfold f'
      have EQ4 := (@Finset.sum_finset_coe Fn _ _ (fun n' => MvPolynomial.C (c n') * f n') (Finset.filter (fun x ↦ ¬c x = 0) Fn.attach))
      have EQ5 : (∑ i : ↑↑(Finset.filter (fun x ↦ ¬c x = 0) Fn.attach), MvPolynomial.C (c ↑i) * f ↑i) = (∑ n' ∈ (Finset.filter (fun x ↦ ¬c x = 0) Fn.attach).attach, MvPolynomial.C (c ↑n') * f ↑n') := by
        simp
      rw [<-EQ5]
      rw [<-EQ4]
      simp
    rw [EQ3]
    exact
      Eq.symm
        (AddZeroClass.zero_add
          (∑ x ∈ Finset.filter (fun x ↦ ¬c x = 0) (Finset.filter (fun n' ↦ True) Finset.univ),
            MvPolynomial.C (c x) * f x))
  clear EQ0
  have MDEG1' : ∀ (n' : Fn'), leading_monomial (f' n') (NE1' n') = m := by
    intro n'
    apply MDEG1
  have NE2' : (∑ (n' : Fn'), (MvPolynomial.C (c' n')) * (f' n')) ≠ 0 := by
    rw [EQ]
    apply NE2
  have MDEG2' : (leading_monomial (∑ (n' : Fn'), (MvPolynomial.C (c' n')) * (f' n')) NE2') < m := by
    have EQ1 : leading_monomial (∑ n' : { x // x ∈ Fn }, MvPolynomial.C (c n') * f n') NE2 = leading_monomial (∑ (n' : Fn'), (MvPolynomial.C (c' n')) * (f' n')) NE2' := by
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
          MvPolynomial.C (if NEQ1 : n' ∈ Fn' then if NEQ2 : n'' ∈ Fn' then c_new' ⟨n', NEQ1⟩ ⟨n'', NEQ2⟩ else 0 else 0) *
            Spol_help (f n') (f n'') (NE1 n') (NE1 n'')) =
      (∑ n' ∈ Finset.filter (fun x ↦ True) Fn.attach,
        ∑ n'' ∈ Finset.filter (fun x ↦ True) Fn.attach,
          MvPolynomial.C (if NEQ1 : n' ∈ Fn' then if NEQ2 : n'' ∈ Fn' then c_new' ⟨n', NEQ1⟩ ⟨n'', NEQ2⟩ else 0 else 0) *
            Spol_help (f n') (f n'') (NE1 n') (NE1 n'')) := by
    simp
  rw [EQ0]
  clear EQ0
  have EQ1 := (Finset.sum_filter_add_sum_filter_not (Finset.filter (fun x ↦ True) Fn.attach)
    (fun n' : Fn => c n' = 0)
    (fun n' => ∑ n'' ∈ Finset.filter (fun x ↦ True) Fn.attach,
          MvPolynomial.C (if NEQ1 : n' ∈ Fn' then if NEQ2 : n'' ∈ Fn' then c_new' ⟨n', NEQ1⟩ ⟨n'', NEQ2⟩ else 0 else 0) *
            Spol_help (f n') (f n'') (NE1 n') (NE1 n'')))
  rw [<- EQ1]
  clear EQ1
  have EQ2 : (∑ x ∈ Finset.filter (fun x ↦ c x = 0) (Finset.filter (fun x ↦ True) Fn.attach),
      ∑ n'' ∈ Finset.filter (fun x ↦ True) Fn.attach,
        MvPolynomial.C (if NEQ1 : x ∈ Fn' then if NEQ2 : n'' ∈ Fn' then c_new' ⟨x, NEQ1⟩ ⟨n'', NEQ2⟩ else 0 else 0) *
          Spol_help (f x) (f n'') (NE1 x) (NE1 n'') = 0) := by
    apply Finset.sum_eq_zero
    intro x
    simp
    intro H
    have MEM : ¬ x ∈ Fn' := by
      unfold Fn'
      simp
      apply H
    apply Finset.sum_eq_zero
    intro x_1
    simp
    rw [@dif_neg (x ∈ Fn') (DEC x) MEM]
    rw [MvPolynomial.C_0]
    exact zero_mul (Spol_help (f x) (f x_1) (NE1 x) (NE1 x_1))
  rw [EQ2]
  clear EQ2
  rw [AddZeroClass.zero_add]
  have EQ1 : (∑ x ∈ Finset.filter (fun x ↦ ¬c x = 0) (Finset.filter (fun x ↦ True) Fn.attach),
        ∑ n'' ∈ Finset.filter (fun x ↦ True) Fn.attach,
          MvPolynomial.C (if NEQ1 : x ∈ Fn' then if NEQ2 : n'' ∈ Fn' then c_new' ⟨x, NEQ1⟩ ⟨n'', NEQ2⟩ else 0 else 0) *
            Spol_help (f x) (f n'') (NE1 x) (NE1 n'')) =
      (∑ x ∈ Finset.filter (fun x ↦ ¬c x = 0) (Finset.filter (fun x ↦ True) Fn.attach),
        ∑ n'' ∈ Finset.filter (fun x ↦ ¬c x = 0) (Finset.filter (fun x ↦ True) Fn.attach),
          MvPolynomial.C (c_new x n'') *
            Spol_help (f x) (f n'') (NE1 x) (NE1 n'')) := by
    apply Finset.sum_congr; simp
    intro x H
    have EQ2 := (Finset.sum_filter_add_sum_filter_not (Finset.filter (fun x ↦ True) Fn.attach)
      (fun n' : Fn => c n' = 0)
      (fun n'' => MvPolynomial.C (if NEQ1 : x ∈ Fn' then if NEQ2 : n'' ∈ Fn' then c_new' ⟨x, NEQ1⟩ ⟨n'', NEQ2⟩ else 0 else 0) *
            Spol_help (f x) (f n'') (NE1 x) (NE1 n'')))
    rw [<- EQ2]
    clear EQ2
    have EQ3 : (∑ x_1 ∈ Finset.filter (fun x ↦ c x = 0) (Finset.filter (fun x ↦ True) Fn.attach),
      MvPolynomial.C (if NEQ1 : x ∈ Fn' then if NEQ2 : x_1 ∈ Fn' then c_new' ⟨x, NEQ1⟩ ⟨x_1, NEQ2⟩ else 0 else 0) *
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
      rw [MvPolynomial.C_0]
      exact zero_mul (Spol_help (f x) (f x') (NE1 x) (NE1 x'))
    rw [EQ3]
    clear EQ3
    rw [AddZeroClass.zero_add]
  rw [EQ1]
  clear EQ1
  rw [Finset.filter_filter]
  have EQ1 : ∑ n' : { x // x ∈ Fn' }, ∑ n'' : { x // x ∈ Fn' }, MvPolynomial.C (c_new' n' n'') * Spol_help (f' n') (f' n'') (NE1' n') (NE1' n'') =
    ∑ n' : { x // x ∈ Fn' }, ∑ n'' : { x // x ∈ Fn' }, MvPolynomial.C (c_new n' n'') * Spol_help (f n') (f n'') (NE1 n') (NE1 n'') := by
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
  have EQ4 := (@Finset.sum_finset_coe Fn _ _ (fun n' => ∑ n'' : { x // x ∈ Fn' }, MvPolynomial.C (c_new n' ↑n'') * Spol_help (f n') (f ↑n'') (NE1 n') (NE1 ↑n'')) (Finset.filter (fun x ↦ ¬c x = 0) Fn.attach))
  have EQ5 : (∑ i : ↑↑(Finset.filter (fun x ↦ ¬c x = 0) Fn.attach),
      ∑ n'' : { x // x ∈ Fn' }, MvPolynomial.C (c_new ↑i ↑n'') * Spol_help (f ↑i) (f ↑n'') (NE1 ↑i) (NE1 ↑n'')) =
      (∑ n' : { x // x ∈ Fn' }, ∑ n'' : { x // x ∈ Fn' }, MvPolynomial.C (c_new ↑n' ↑n'') * Spol_help (f ↑n') (f ↑n'') (NE1 ↑n') (NE1 ↑n'')) := by
    simp
  rewrite [<-EQ5]
  clear EQ5
  have EQ6 : (∑ i ∈ Finset.filter (fun x ↦ ¬c x = 0) Fn.attach,
    ∑ n'' : { x // x ∈ Fn' }, MvPolynomial.C (c_new i ↑n'') * Spol_help (f i) (f ↑n'') (NE1 i) (NE1 ↑n'')) =
    (∑ x ∈ Finset.filter (fun a ↦ True ∧ ¬c a = 0) Fn.attach,
      ∑ n'' ∈ Finset.filter (fun a ↦ True ∧ ¬c a = 0) Fn.attach,
        MvPolynomial.C (c_new x n'') * Spol_help (f x) (f n'') (NE1 x) (NE1 n'')) := by
    clear EQ4
    simp
    apply Finset.sum_congr; simp
    intro x H
    have EQ4 := (@Finset.sum_finset_coe Fn _ _ (fun n'' => MvPolynomial.C (c_new x n'') * Spol_help (f x) (f ↑n'') (NE1 x) (NE1 ↑n'')) (Finset.filter (fun x ↦ ¬c x = 0) Fn.attach))
    have EQ5 : (∑ i : ↑↑(Finset.filter (fun x ↦ ¬c x = 0) Fn.attach), MvPolynomial.C (c_new x ↑i) * Spol_help (f x) (f ↑i) (NE1 x) (NE1 ↑i)) =
      (∑ n'' ∈ Fn'.attach, MvPolynomial.C (c_new x ↑n'') * Spol_help (f x) (f ↑n'') (NE1 x) (NE1 ↑n'')) := by
      simp
    rewrite [<-EQ5]
    clear EQ5
    rw [<-EQ4]
    simp
  rw [<-EQ6]
  apply EQ4

-- lemma Spol_help_lemma5_help [DecidableEq σ] [DecidableEq R] [Field R] [ord : MonomialOrder σ ] n (c : Fin n -> R) (f : Fin n -> MvPolynomial σ R)
--   (m : Monomial σ)
--   (NE0 : ∀ (n' : Fin n), c n' ≠ 0)
--   (NE1 : ∀ (n' : Fin n), f n' ≠ 0)
--   (MDEG1 : ∀ (n' : Fin n), leading_monomial (f n') (NE1 n') = m)
--   (NE2 : (∑ (n' : Fin n), (MvPolynomial.C (c n')) * (f n')) ≠ 0)
--   (MDEG2 : (leading_monomial (∑ (n' : Fin n), (MvPolynomial.C (c n')) * (f n')) NE2) < m) :
--   ∃ (c' : Fin n -> Fin n -> R),
--   (∑ (n' : Fin n), (MvPolynomial.C (c n')) * (f n')) = (∑ (n' : Fin n), ∑ (n'' : Fin n), (MvPolynomial.C (c' n' n'')) * (Spol_help (f n') (f n'') (NE1 n') (NE1 n''))) := by
--   let d := (fun n' => leading_coeff (f n') (NE1 n'))
--   -- induction' n with np IH; simp
--   -- simp
--   sorry

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
