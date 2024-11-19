-- import GB.CFinsupp
import GB.Monomial
import Mathlib.Algebra.MvPolynomial.Degrees

-- -- Finite Variable Polynomial
-- def FiniteVarPoly (σ : Type) (R : Type) [CommRing R] := CFinsupp (Monomial σ) R

-- @[simp]
-- instance (σ : Type) [CommRing R] : Zero (FiniteVarPoly σ R) where
--   zero := (0 : (CFinsupp (Monomial σ) R))

instance [CommRing R] : FunLike (MvPolynomial σ R) (Monomial σ) R := Finsupp.instFunLike

def is_monomial  [CommRing R] (p : MvPolynomial σ R)  :=
  ∃! m, m ∈ p.support ∧ True

def mono_poly_mono [CommRing R] [Nontrivial R] : ∀(m : Monomial σ), is_monomial (@toMvPolynomial R _ _ m) := by {
  intros m;unfold is_monomial;unfold toMvPolynomial
  rw [<-MvPolynomial.single_eq_monomial];unfold MvPolynomial.support;unfold Finsupp.single;simp
}

lemma is_monomial_nonzero [CommRing R] {p : MvPolynomial σ R} :
    is_monomial p -> p ≠ 0 := by
  intro p_ismon
  rcases p_ismon with ⟨p', ⟨h1,_⟩, _⟩; rw [MvPolynomial.ne_zero_iff];
  exists p'; rw[MvPolynomial.coeff];
  apply (p.mem_support_toFun p').mp; assumption

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

noncomputable def MvPolynomial.instSub  [CommRing R] : Sub (MvPolynomial σ R) where
  sub := fun a b => Finsupp.instSub.sub a b

def MvPolynomial.toMonomial [CommRing R] (p : MvPolynomial σ R) (h : is_monomial p) :=
  Finset.choose (fun _ => True) p.support h

def Monomial.instMembership [CommRing R] [DecidableEq σ] : Membership (Monomial σ) (Set (MvPolynomial σ R)) where
  mem := fun s m => (Monomial.toMvPolynomial.coe m) ∈ s

def MvPolynomial.instMembership [CommRing R] [DecidableEq σ] : Membership (MvPolynomial σ R) (Set (Monomial σ)) where
  mem := fun s p => exists h : (is_monomial p), (MvPolynomial.toMonomial p h) ∈ s

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
