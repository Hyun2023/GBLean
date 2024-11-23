-- import GB.CFinsupp
import GB.Monomial
import Mathlib.Algebra.MvPolynomial.Degrees

-- -- Finite Variable Polynomial
-- def FiniteVarPoly (σ : Type) (R : Type) [CommRing R] := CFinsupp (Monomial σ) R

-- @[simp]
-- instance (σ : Type) [CommRing R] : Zero (FiniteVarPoly σ R) where
--   zero := (0 : (CFinsupp (Monomial σ) R))

instance [CommRing R] : FunLike (MvPolynomial σ R) (Monomial σ) R := Finsupp.instFunLike

def is_monomial'  [CommRing R] (p : MvPolynomial σ R)  :=
  ∃! m, m ∈ p.support ∧ True

-- def mono_poly_mono [CommRing R] [Nontrivial R] : ∀(m : Monomial σ), is_monomial (@toMvPolynomial R _ _ m) := by {
--   intros m;unfold is_monomial;unfold toMvPolynomial
--   rw [<-MvPolynomial.single_eq_monomial];unfold MvPolynomial.support;unfold Finsupp.single;simp
-- }

def is_monomial  [CommRing R] (p : MvPolynomial σ R)  :=
  (∃! m, m ∈ p.support ∧ True) ∧ (∀ m, m ∈ p.support -> p m = 1)

def mono_poly_mono [CommRing R] [Nontrivial R] : ∀(m : Monomial σ), is_monomial (@toMvPolynomial R _ _ m) := by {
  intros m; unfold is_monomial; unfold toMvPolynomial
  rw [<-MvPolynomial.single_eq_monomial]; unfold MvPolynomial.support; unfold Finsupp.single; simp
  rw [DFunLike.coe, instFunLikeMvPolynomialMonomial, Finsupp.instFunLike]; simp
}

def is_monomial_fst [CommRing R] {p : MvPolynomial σ R} (p_monomial : is_monomial p) :
  is_monomial' p :=
  let ⟨h1, _⟩ := p_monomial
  h1

lemma is_monomial'_nonzero [CommRing R] {p : MvPolynomial σ R} :
    is_monomial' p -> p ≠ 0 := by
  intro p_ismon'
  obtain ⟨m, ⟨⟨P1, _⟩, P2⟩⟩ := p_ismon'
  rw [MvPolynomial.ne_zero_iff]
  use m; rw [MvPolynomial.coeff]
  apply (p.mem_support_toFun m).mp; assumption

lemma is_monomial_nonzero [CommRing R] {p : MvPolynomial σ R} :
    is_monomial p -> p ≠ 0 := by
  intro p_ismon
  apply is_monomial'_nonzero
  apply is_monomial_fst
  apply p_ismon

-- lemma is_monomial_true [CommRing R] (m : σ →₀ ℕ) :
--     is_monomial (@MvPolynomial.monomial R σ _ m 1) := by
--   constructor; any_goals exact m
--   constructor
--   . simp; apply ((MvPolynomial.monomial m 1).mem_support_toFun m).mp
--     have := @MvPolynomial.support_monomial _ _ 1 m _ (by apply isFalse; linarith)
--     simp at this;
--     -- rw [this]
--     -- have G: m∈{m} := sorry
--     sorry
--   . intro y h
--     have := @MvPolynomial.support_monomial _ _ 1 m _ (by apply isFalse; linarith)
--     simp at this;
--     -- rw [this] at h
--     sorry

noncomputable def MvPolynomial.instSub [CommRing R] : Sub (MvPolynomial σ R) where
  sub := fun a b => Finsupp.instSub.sub a b

noncomputable def MvPolynomial.instNeg [CommRing R] : Neg (MvPolynomial σ R) where
  neg := fun a => Finsupp.instSub.sub 0 a

def MvPolynomial.instSub_sound [CommRing R] : ∀ (f t : MvPolynomial σ R), f = t + (MvPolynomial.instSub.sub f t) := by
  intro f t
  rw [Sub.sub, instSub]; simp
  rw [Sub.sub, Finsupp.instSub]; simp
  rw [HAdd.hAdd, instHAdd]; simp
  rw [Add.add, Distrib.toAdd, NonUnitalNonAssocSemiring.toDistrib]; simp
  rw [AddSemigroup.toAdd, AddMonoid.toAddSemigroup, AddCommMonoid.toAddMonoid, NonUnitalNonAssocSemiring.toAddCommMonoid, NonAssocSemiring.toNonUnitalNonAssocSemiring, Semiring.toNonAssocSemiring]; simp
  rw [NonUnitalSemiring.toNonUnitalNonAssocSemiring, Semiring.toNonUnitalSemiring, CommSemiring.toSemiring, commSemiring, AddMonoidAlgebra.commSemiring]; simp
  rw [NonUnitalCommSemiring.toNonUnitalSemiring, AddMonoidAlgebra.nonUnitalCommSemiring]; simp
  rw [AddMonoidAlgebra.nonUnitalSemiring]; simp
  rw [AddMonoidAlgebra.nonUnitalNonAssocSemiring]; simp
  rw [AddMonoid.toAddSemigroup, AddCommMonoid.toAddMonoid, Finsupp.instAddCommMonoid]; simp
  rw [Finsupp.instAddMonoid]; simp
  rw [AddZeroClass.toAdd]; simp
  rw [Finsupp.instAdd]; simp
  ext m
  rw [coeff, coeff]; simp
  exact Eq.symm (add_eq_of_eq_sub' rfl)

def MvPolynomial.instSub_sound' [CommRing R] : ∀ (f t : MvPolynomial σ R), f = (MvPolynomial.instSub.sub f t) + t := by
  intro f t
  have EQ' : (MvPolynomial.instSub.sub f t) + t = t + (MvPolynomial.instSub.sub f t) := by
    symm
    apply AddCommMagma.add_comm
  rw [EQ']
  apply MvPolynomial.instSub_sound

def MvPolynomial.instSub_sound'' [CommRing R] : ∀ (f g : MvPolynomial σ R), MvPolynomial.instSub.sub f g = f + (MvPolynomial.instSub.sub 0 g) := by
  intro f g
  have EQ : MvPolynomial.instSub.sub f g + g = (f + (MvPolynomial.instSub.sub 0 g)) + g := by
    rw [<- MvPolynomial.instSub_sound']
    have EQ' : f + MvPolynomial.instSub.sub 0 g + g = f + (MvPolynomial.instSub.sub 0 g + g) := by
      apply add_assoc
    rw [EQ']
    rw [<- MvPolynomial.instSub_sound' 0 g]
    exact Eq.symm (AddMonoid.add_zero f)
  have RCA : IsRightCancelAdd (MvPolynomial σ R) := by
    apply Finsupp.instIsRightCancelAdd
  have AC := (@add_right_cancel _ _ _ (MvPolynomial.instSub.sub f g) g (f + (MvPolynomial.instSub.sub 0 g)))
  exact AC EQ

def MvPolynomial.instSub_smul [CommRing R] : ∀ (f g : MvPolynomial σ R) (c : R), c • (MvPolynomial.instSub.sub f g) = MvPolynomial.instSub.sub (c • f) (c • g) := by
  intro f g c
  rw [MvPolynomial.instSub_sound'']
  nth_rewrite 2 [MvPolynomial.instSub_sound'']
  have EQ : c • (f + MvPolynomial.instSub.sub 0 g) = c • f + c • (MvPolynomial.instSub.sub 0 g) := by
    apply DistribSMul.smul_add
  rw [EQ]
  clear EQ
  have EQ : c • MvPolynomial.instSub.sub 0 g = MvPolynomial.instSub.sub 0 (c • g) := by
    have EQ' : c • MvPolynomial.instSub.sub 0 g + c • g = MvPolynomial.instSub.sub 0 (c • g) + c • g := by
      rw [<- MvPolynomial.instSub_sound']
      rw [<- DistribSMul.smul_add]
      rw [<- MvPolynomial.instSub_sound']
      exact DistribMulAction.smul_zero c
    have RCA : IsRightCancelAdd (MvPolynomial σ R) := by
      apply Finsupp.instIsRightCancelAdd
    have AC := (@add_right_cancel _ _ _ (c • MvPolynomial.instSub.sub 0 g) (c • g) (MvPolynomial.instSub.sub 0 (c • g)))
    exact AC EQ'
  rw [EQ]

def MvPolynomial.toMonomial [CommRing R] [DecidableEq R] (p : MvPolynomial σ R) (h : is_monomial p) :=
  Finset.choose (fun _ => True) p.support (is_monomial_fst h)

def Monomial.instMembership [CommRing R] [DecidableEq σ] [DecidableEq R] : Membership (Monomial σ) (Set (MvPolynomial σ R)) where
  mem := fun s m => (Monomial.toMvPolynomial.coe m) ∈ s

def MvPolynomial.instMembership [CommRing R] [DecidableEq σ] [DecidableEq R] : Membership (MvPolynomial σ R) (Set (Monomial σ)) where
  mem := fun s p => exists h : (is_monomial p), (MvPolynomial.toMonomial p h) ∈ s

lemma polynomial_scalarmult_nonzero_help [DecidableEq σ] [Field R] [DecidableEq R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0)
  (c : R) (NE : c ≠ 0) : p.support = (c • p).support := by
  rw [HSMul.hSMul, instHSMul]; simp
  rw [SMul.smul, Algebra.toSMul, MvPolynomial.algebra, AddMonoidAlgebra.algebra]; simp
  rw [SMulZeroClass.toSMul, AddMonoidAlgebra.smulZeroClass, Finsupp.smulZeroClass]; simp
  rw [Finsupp.mapRange, Finsupp.onFinset]; simp
  have EQ' : p.support = Finset.filter (fun a ↦ ¬c * p a = 0) p.support := by
    symm
    rw [Finset.filter_eq_self]
    intro x H
    have NEQ : p x ≠ 0 := by
      have EQ'' := (p.mem_support_toFun x)
      have EQ''' : p.toFun x ≠ 0 := by
        rw [<- EQ'']
        apply H
      apply EQ'''
    exact mul_ne_zero NE NEQ
  rw [EQ']
  simp; rfl

lemma polynomial_scalarmult_nonzero [DecidableEq σ] [Field R] [DecidableEq R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0)
  (c : R) (NE : c ≠ 0) : c • p ≠ 0 := by
  rw [<-MvPolynomial.support_nonempty]
  rw [<-MvPolynomial.support_nonempty] at p_nonzero
  have EQ : (p.support = (c • p).support) := by
    apply polynomial_scalarmult_nonzero_help
    . rw [<-MvPolynomial.support_nonempty]
      assumption
    . assumption
  rw [<- EQ]
  assumption

lemma leading_coeff_scalarmult [DecidableEq σ] [Field R] [DecidableEq R] [MonomialOrder σ ] (p : MvPolynomial σ R) (p_nonzero : p ≠ 0)
  (c : R) (NE : c ≠ 0) : c * (leading_coeff p p_nonzero) = leading_coeff (c • p) (polynomial_scalarmult_nonzero p p_nonzero c NE) := by
  unfold leading_coeff
  rw [MvPolynomial.coeff, MvPolynomial.coeff]
  have EQ : leading_monomial p p_nonzero = leading_monomial (c • p) (polynomial_scalarmult_nonzero p p_nonzero c NE) := by
    unfold leading_monomial
    unfold monomials
    have EQ' : p.support = (c • p).support := by
      apply polynomial_scalarmult_nonzero_help <;> assumption
    congr!
  rw [<- EQ]
  rfl

-- lemma zero_is_not_mon  [CommRing R] : ¬(is_monomial (0 : (FiniteVarPoly σ R) )) := by
--   intros ismon
--   unfold is_monomial at *
--   have H : (0 : (FiniteVarPoly σ R) ).support = ∅ := by rfl
--   simp [H] at ismon

-- noncomputable def ofFiniteVarPoly [DecidableEq σ] [CommRing R] : Coe (FiniteVarPoly σ R) (MvPolynomial σ R) where
--   coe m := Finsupp.mapDomain ofCFinsupp.coe (ofCFinsupp.coe m)

-- noncomputable instance toFiniteVarPoly [DecidableEq σ] [CommRing R] : Coe (MvPolynomial σ R) (FiniteVarPoly σ R) where
--   coe m := toCFinsupp.coe (Finsupp.mapDomain toCFinsupp.coe m)

-- lemma toFiniteVarPoly_ofFiniteVarPoly_inverse [DecidableEq σ] [CommRing R] : ∀ p, (@toFiniteVarPoly σ R _ _).coe (ofFiniteVarPoly.coe p) = p := by
--   intro p; rw [Coe.coe, Coe.coe, toFiniteVarPoly, ofFiniteVarPoly]; simp
--   rw [← Finsupp.mapDomain_comp]
--   have H : ((@toCFinsupp σ ℕ _ _).coe ∘ (@ofCFinsupp σ ℕ _ _).coe = id) := by
--     ext x; simp; rw [toCFinsupp_ofCFinsupp_inverse]
--   rw [H]; simp
--   rw [Coe.coe, Coe.coe]
--   nth_rewrite 2 [← toCFinsupp_ofCFinsupp_inverse p, Coe.coe];
--   rw [Coe.coe]

-- lemma ofFiniteVarPoly_toFiniteVarPoly_inverse [DecidableEq σ] [CommRing R] : ∀ p, (@ofFiniteVarPoly σ R _ _).coe (toFiniteVarPoly.coe p) = p := by
--   intro p; rw [Coe.coe, Coe.coe, toFiniteVarPoly, ofFiniteVarPoly]; simp
--   rw [ofCFinsupp_toCFinsupp_inverse]
--   rw [← Finsupp.mapDomain_comp]
--   have H : ((@ofCFinsupp σ ℕ _ _).coe ∘ (@toCFinsupp σ ℕ _ _).coe = id) := by
--     ext x; simp; rw [ofCFinsupp_toCFinsupp_inverse]
--   rw [H]; simp

-- instance FiniteVarPoly.instFunLike [DecidableEq σ] [CommRing R] : FunLike (FiniteVarPoly σ R) (Monomial σ) R := CFinsupp.instFunLike

-- instance MvPolynomial.instFunLike [DecidableEq σ] [CommRing R] : FunLike (MvPolynomial σ R) (σ→₀ℕ) R where
--   coe m := m.toFun
--   coe_injective' := Finsupp.instFunLike.2

-- lemma coeff_equiv [DecidableEq σ] [CommRing R] :
--   ∀ (m : Monomial σ) (p : FiniteVarPoly σ R), @MvPolynomial.coeff R σ _ m p = p m := by
--   intro m p; rw [MvPolynomial.coeff]; rw [Finsupp.mapDomain_apply]
--   . simp; rcases (em (m ∈ p.support)) with h|h <;> simp [h]
--     . rw [CFinsupp.toFun, DFunLike.coe, FiniteVarPoly.instFunLike, CFinsupp.instFunLike]; simp
--       rw [Coe.coe, ofCFinsupp]; simp
--       rw [dif_pos]
--     . rw [DFunLike.coe, FiniteVarPoly.instFunLike, CFinsupp.instFunLike]; simp
--       rw [Coe.coe, ofCFinsupp]; simp
--       rw [dif_neg]
--       apply h
--   . intros f1 f2 EQ; simp at EQ
--     obtain ⟨EQ1, EQ2⟩ := EQ
--     sorry

-- instance [DecidableEq σ] [CommRing R] [NeZero (1:R)] :
--     Coe (Monomial σ) (FiniteVarPoly σ R) where
--   coe := fun m => {
--     support := {m}
--     toFun := fun _ => 1
--     nonzero := by intro; simp
--   }

-- instance FiniteVarPoly.instAdd [DecidableEq σ] [DecidableEq R] [CommRing R] : Add (FiniteVarPoly σ R) where
--   add := CFinsupp.binop' (fun (x y : R) => x+y)

-- instance FiniteVarPoly.instSub [DecidableEq σ] [DecidableEq R] [CommRing R] : Sub (FiniteVarPoly σ R) where
--   sub := CFinsupp.binop' (fun (x y : R) => x-y)

-- instance MvPolynomial.instLinearOrder [DecidableEq σ] [DecidableEq R] [CommRing R] [LinearOrder σ] : LinearOrder (MvPolynomial σ R) :=
--   sorry
  -- @CFinsuppInstLinearOrder (Monomial σ) R _ _ _ Monomial_lex _

-- Preorder of MvPolynomial based on degree
instance [CommRing R] : Preorder (MvPolynomial σ R) where
  le  p₁ p₂ := p₁.totalDegree<= p₂.totalDegree
  le_refl := by intros; simp
  le_trans := by intros; simp; transitivity <;> assumption

-- noncomputable def MvPolynomial.toList [DecidableEq R] [CommRing R] [LinearOrder σ] (s : Finset (MvPolynomial σ R)) : List (MvPolynomial σ R) :=
--   @WellFoundedLT.fix
--     (Finset (MvPolynomial σ R)) _ Finset.wellFoundedLT
--     (fun _ => List (MvPolynomial σ R))
--     (fun s IH => if c: s.Nonempty then  by
--       simp at IH
--       let p := Set.IsWF.min (Finset.isWF s) c
--       have pIn : p ∈ s := Set.IsWF.min_mem (Finset.isWF s) c
--       have Hsubset : s \ {p} ⊂ s := by
--         refine Finset.sdiff_ssubset ?h ?ht
--         . exact Finset.singleton_subset_iff.mpr pIn
--         . exact Finset.singleton_nonempty p
--       have t := IH (s \ {p}) Hsubset
--       exact p::t
--       else [])
--     s

-- lemma MvPolynomial.to_List_sound [DecidableEq R] [CommRing R] [LinearOrder σ] (s : Finset (MvPolynomial σ R)) :
--   s.toList.toFinset = s := by
--   -- apply (WellFoundedLT.induction s)
--   -- clear s; intro s _
--   -- rcases em s.Nonempty <;>
--   simp [toList]

-- def FiniteVarPoly.toList_sound [DecidableEq σ] [DecidableEq R] [CommRing R] [LinearOrder σ] [LinearOrder R] (s : Finset (FiniteVarPoly σ R)) : List.toFinset (FiniteVarPoly.toList s) = s := by
--   apply Finset.ext
--   intro a
--   constructor <;> intro H
--   . rw [FiniteVarPoly.toList] at H
--     simp at H
--     apply H
--   . rw [FiniteVarPoly.toList]
--     simp
--     apply H

-- def FiniteVarPoly.monomial_toList [DecidableEq σ] [DecidableEq R] [CommRing R] [LinearOrder σ] (s : FiniteVarPoly σ R) : List (Monomial σ) :=
--   Finset.sort (@Monomial_lex σ _ _).le s.support

-- def FiniteVarPoly.monomial_toList_withR [DecidableEq σ] [DecidableEq R] [CommRing R] [LinearOrder σ] (s : FiniteVarPoly σ R) : List (Monomial σ × R) :=
--   List.map (fun m => (m, s m)) (FiniteVarPoly.monomial_toList s)

-- def zeropoly [DecidableEq σ] [CommRing R] : FiniteVarPoly σ R :=
--   ⟨Finset.empty, fun _ => 0, by
--     rintro ⟨x,_,_⟩
--   ⟩

-- def monomial_coeff_poly [DecidableEq σ] [DecidableEq R] [CommRing R] (m : Monomial σ) (c : R) : FiniteVarPoly σ R :=
--   if Ne : c ≠ 0 then
--     ⟨{ m }, fun _ => c, by
--       intro x; simp; apply Ne
--     ⟩
--   else zeropoly

-- def FiniteVarPoly.List_indiv_mul [DecidableEq σ] [DecidableEq R] [CommRing R] [LinearOrder σ] (l : List (Monomial σ × R)) (m : Monomial σ × R) : FiniteVarPoly σ R :=
--   match l with
--   | .nil => zeropoly
--   | .cons m' l' => FiniteVarPoly.List_indiv_mul l' m + monomial_coeff_poly (Prod.fst m * Prod.fst m') (Prod.snd m * Prod.snd m')

-- def FiniteVarPoly.List_List_mul [DecidableEq σ] [DecidableEq R] [CommRing R] [LinearOrder σ] (l1 l2 : List (Monomial σ × R)) : FiniteVarPoly σ R :=
--   match l1 with
--   | .nil => zeropoly
--   | .cons m l1' => FiniteVarPoly.List_indiv_mul l2 m + FiniteVarPoly.List_List_mul l1' l2

-- def FiniteVarPoly.poly_mul [DecidableEq σ] [DecidableEq R] [CommRing R] [LinearOrder σ] (p1 p2 : FiniteVarPoly σ R) : FiniteVarPoly σ R :=
--   FiniteVarPoly.List_List_mul (FiniteVarPoly.monomial_toList_withR p1) (FiniteVarPoly.monomial_toList_withR p2)

-- instance FiniteVarPoly.instMul [DecidableEq σ] [DecidableEq R] [CommRing R] [LinearOrder σ] : Mul (FiniteVarPoly σ R) where
--   mul := FiniteVarPoly.poly_mul

-- instance [DecidableEq σ] [DecidableEq R] [CommRing R] : DecidableEq (FiniteVarPoly σ R) := CFinsupp.DecidableEq

-- instance [CommRing R] : CommSemiring (FiniteVarPoly σ R) := sorry


-- def monomials [DecidableEq σ] [CommRing R] (p : FiniteVarPoly σ R) : Finset (Monomial σ) :=
--   p.support

-- -- Leading Monomial and Term
-- def isZeroEquiv [DecidableEq σ] [CommRing R] :
--     ∀ (m : FiniteVarPoly σ R), m = 0 ↔ (m : MvPolynomial σ R) = 0 := by
--   -- intro m; constructor <;> intro h
--   -- . subst h; rw [Coe.coe, ofFiniteVarPoly]; simp
--   --   apply Finsupp.mapDomain_apply
--   --   sorry
--   sorry
-- def isNonZeroEquiv [DecidableEq σ] [CommRing R] :
--     ∀ (m : FiniteVarPoly σ R), m ≠ 0 ↔ (m : MvPolynomial σ R) ≠ 0 := by
--   intro m; constructor <;> intro h g <;> apply h
--   rw [isZeroEquiv]; assumption
--   rw [← isZeroEquiv]; assumption

-- def term_exists [DecidableEq σ] [CommRing R] (p : FiniteVarPoly σ R) (p_nonzero : p ≠ 0) : (monomials p).Nonempty := by
--   -- have exM : exists m, p m ≠ 0 := by
--   --   rw [Ne, isZeroEquiv, ← Ne] at p_nonzero
--   --   rw [MvPolynomial.ne_zero_iff] at p_nonzero
--   --   rcases p_nonzero with ⟨m, p_nonzero⟩
--   --   exists m; simp; rw [coeff_equiv m] at p_nonzero
--   --   exact p_nonzero
--   -- rcases exM with ⟨m, mcond⟩
--   -- constructor; any_goals exact (toMonomial.coe m)
--   -- rw [monomials, toCFinsupp_emb]
--   -- apply Finset.mem_map.mpr; simp
--   -- exists (m)
--   sorry

-- def leading_monomial [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : FiniteVarPoly σ R) (p_nonzero : p ≠ 0): Monomial σ :=
--   @Finset.max' _ ord.toLinearOrder (monomials p)
--   (term_exists p p_nonzero)

-- -- instance FiniteVarPoly.instMul [DecidableEq σ] [DecidableEq R] [CommRing R] : Mul (FiniteVarPoly σ R) where
-- --   mul :=

-- -- instance FiniteVarPoly_CommRing [CommRing R] : CommRing (FiniteVarPoly σ R) where

-- def term_exists2 [DecidableEq σ] [CommRing R] (p : FiniteVarPoly σ R) (p_nonzero : ¬CFinsuppequiv p zeropoly) : (CFinsupp.support p).Nonempty := by
--   by_contra NE
--   apply p_nonzero
--   unfold CFinsuppequiv
--   constructor
--   . unfold zeropoly; simp
--     rw [Finset.not_nonempty_iff_eq_empty] at NE
--     rw [NE]
--     rfl
--   . intro a; intro in1; intro in2
--     unfold zeropoly at in2; simp at in2
--     exfalso
--     apply Finset.not_mem_empty at in2
--     apply in2

-- -- def leading_monomial2 [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : FiniteVarPoly σ R) (p_nonzero : p ≠ zeropoly): Monomial σ :=
-- --   @Finset.max' _ ord.toLinearOrder (CFinsupp.support p)
-- --   (term_exists2 p p_nonzero)

-- def leading_monomial2 [DecidableEq σ] [CommRing R] [ord : MonomialOrder σ ] (p : FiniteVarPoly σ R) (p_nonzero : (CFinsupp.support p).Nonempty): Monomial σ :=
--   @Finset.max' _ ord.toLinearOrder (CFinsupp.support p)
--   p_nonzero

-- -- def coeff2 [DecidableEq σ] [CommRing R] (p : FiniteVarPoly σ R)

-- def leading_coeff2 [DecidableEq σ] [CommRing R] [MonomialOrder σ ] (p : FiniteVarPoly σ R) (p_nonzero : (CFinsupp.support p).Nonempty): R :=
--   p.toFun ⟨leading_monomial2 p p_nonzero, by
--     unfold leading_monomial2
--     apply Finset.max'_mem
--   ⟩
