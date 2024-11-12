import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Lex

-- Computable version of Finsupp

section CFinsupp

-- Definition of CFinsupp and related operation
structure CFinsupp (A B : Type) [Zero B] : Type where
  support : Finset A
  toFun : support → B
  nonzero : ∀x, toFun x ≠ 0

def CFinsuppequiv [Zero B] (c1 c2 : CFinsupp A B) :=
  c1.support = c2.support ∧ ∀a (in1 : a ∈ c1.support) (in2 : a ∈ c2.support), c1.toFun ⟨a, in1⟩ = c2.toFun ⟨a, in2⟩

def CFinsuppExists [Zero B] : (Inhabited (CFinsupp A B)) :=
  ⟨Finset.empty, fun _ => 0, by
    rintro ⟨x,_,_⟩
  ⟩

instance ofCFinsupp [DecidableEq A] [Zero B] : Coe (CFinsupp A B) (A →₀ B) where
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

lemma CFinsupp_instFunLike_injective [DecidableEq A] [Zero B] : Function.Injective (fun m => ((@ofCFinsupp A B _).coe m).toFun) := by
    rintro ⟨A₁,p₁,nonzero₁⟩ ⟨A₂,p₂,nonzero₂⟩ h
    rw [Coe.coe, ofCFinsupp] at h; simp at h
    apply funEq at h
    have G1: A₁ = A₂ := by
      apply (@Finset.instIsAntisymmSubset A).antisymm
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
    -- rw [G1] at *
    subst G1
    congr!
    ext x; have h2 := h x
    rcases x with ⟨x,inA⟩; simp [inA] at h2
    assumption


instance toCFinsupp [DecidableEq A] [Zero B] : Coe (A →₀ B) (CFinsupp A B) where
  coe := fun m => ⟨
    m.support,
    fun x => m.toFun x.1,
    by
      rintro ⟨x,p⟩; simp
      apply (m.mem_support_toFun x).mp
      assumption
    ⟩

lemma toCFinsupp_injective [DecidableEq A] [Zero B] : Function.Injective (@toCFinsupp A B _).coe := by
  simp [Function.Injective]
  rintro ⟨A₁,p₁,nonzero₁⟩ ⟨A₂,p₂,nonzero₂⟩ h
  rw [Coe.coe, toCFinsupp] at h; simp at h
  rcases h with ⟨h1, h2⟩
  subst h1
  simp at h2
  congr!
  apply funEq at h2
  ext x
  by_cases hin: x∈ A₁
  {
    have hx := h2 ⟨x,hin⟩
    assumption
  }
  {
    have p1_zero :=  (not_iff_not.mpr (nonzero₁ x) ).mp hin
    have p2_zero := (not_iff_not.mpr (nonzero₂ x) ).mp hin
    simp at p1_zero;simp at p2_zero
    rw [p1_zero,p2_zero]
  }

def toCFinsupp_emb [DecidableEq A] [Zero B] : (A →₀ B) ↪ (CFinsupp A B) where
  toFun := (@toCFinsupp A _).coe
  inj' := toCFinsupp_injective

lemma toCFinsupp_ofCFinsupp_inverse [DecidableEq A] [Zero B] : ∀ x, (@toCFinsupp A B _).coe (ofCFinsupp.coe x) = x := by
  intro x; rw [Coe.coe, Coe.coe, toCFinsupp, ofCFinsupp]; simp

lemma ofCFinsupp_toCFinsupp_inverse [DecidableEq A] [Zero B] : ∀ x, (@ofCFinsupp A B _).coe (toCFinsupp.coe x) = x := by
  rintro ⟨A,p,h⟩ ; rw [Coe.coe, Coe.coe, toCFinsupp, ofCFinsupp]; simp
  ext x; have h' := h x
  rcases em (x ∈ A) with inA|inA <;> simp [inA]
  symm; by_contra!; rw [← h'] at this; contradiction

instance CFinsupp.instFunLike [DecidableEq A] [Zero B] : FunLike (CFinsupp A B) A B where
  coe := fun m => ((@ofCFinsupp A B _).coe m).toFun
  coe_injective' := CFinsupp_instFunLike_injective

lemma Finset.union_contradiction [DecidableEq X] {A B : Finset X} :
    (x ∉ A) -> (x ∉ B) -> x ∉ (A ∪ B) := by
  intro h1 h2
  apply Finset.not_mem_union.mpr
  constructor <;> assumption

-- use only if ∀ x y, (x≠0) && (y≠0) -> op x y ≠ 0
def CFinsupp.binop [DecidableEq A] [DecidableEq B] [Zero B] (op : B → B → B)
  (preserves_nonzero : ∀ x y, (x≠0) && (y≠0) -> op x y ≠ 0):
    CFinsupp A B → CFinsupp A B → CFinsupp A B :=
  fun f g =>  ⟨
    f.1 ∪ g.1,
    fun ⟨x, infg⟩ =>
      if pf: x∈f.1 then
        if pg: x∈g.1 then op (f.2 ⟨x, pf⟩) (g.2 ⟨x, pg⟩)
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
        have nonzeroG := g.nonzero ⟨x,pg⟩
        apply preserves_nonzero at G; assumption
        simp; constructor <;> assumption
      . have nonzeroF := f.nonzero ⟨x,pf⟩
        contradiction
      . have nonzeroG := g.nonzero ⟨x,pg⟩
        contradiction
      . rcases infg <;> contradiction
  ⟩

lemma CFinsupp.binop_correct [DecidableEq A] [DecidableEq B] [Zero B] (op : B → B → B)
  (preserves_nonzero : ∀ x y, (x≠0) && (y≠0) <-> op x y ≠ 0) :
  ∀ (m₁ m₂ : CFinsupp A B), CFinsupp.binop op (fun x y => (preserves_nonzero x y).mp) m₁ m₂ =
  (Finsupp.zipWith op
    (by by_contra G; push_neg at G; rw [← preserves_nonzero 0 0] at G; simp at G)
    m₁ m₂ : A →₀ B) := by
  intro x y; rw [binop, Finsupp.zipWith, Finsupp.onFinset]; congr! <;> simp
  . symm
    let p := (fun x_1 ↦ ¬op (if p : x_1 ∈ x.support then x.toFun ⟨x_1, p⟩ else 0) (if p : x_1 ∈ y.support then y.toFun ⟨x_1, p⟩ else 0) = 0)
    have : DecidablePred p := by intro x_1; sorry
    have := (@Finset.filter_eq_self A p _ (x.support ∪ y.support)).mpr; simp at this
    -- apply this
    sorry
  sorry

instance CFinsupp.binop_commutative [DecidableEq A] [DecidableEq B] [Zero B] (op : B → B → B) [Std.Commutative op]
  (preserves_nonzero : ∀ x y, (x≠0) && (y≠0) -> op x y ≠ 0) : Std.Commutative (@CFinsupp.binop A _ _ _ _ op preserves_nonzero) where
  comm := by
    intro a b
    rw [binop, binop]; simp
    constructor
    . rw [Finset.union_comm]
    . apply Function.hfunext
      . have H : (a.support ∪ b.support = b.support ∪ a.support) := by
          rw [Finset.union_comm]
        rw [H]
      . intro x1 x2 HEQ
        simp
        have EQ' : x1.1 = x2.1 := by
          rw [<- @Subtype.heq_iff_coe_eq _ (fun x => x ∈ a.support ∪ b.support) (fun x => x ∈ b.support ∪ a.support)]
          . apply HEQ
          . intro x
            have H : (a.support ∪ b.support = b.support ∪ a.support) := by
              rw [Finset.union_comm]
            rw [H]
        rw [toFun, toFun]
        rcases em (x1.1 ∈ a.support) with INa|nINa
        . rw [dif_pos INa]
          have INa' : x2.1 ∈ a.support := by
            rw [<- EQ']
            apply INa
          rcases em (x1.1 ∈ b.support) with INb|nINb
          . rw [dif_pos INb]
            have INb' : x2.1 ∈ b.support := by
              rw [<- EQ']
              apply INb
            rw [dif_pos INb']
            rw [dif_pos INa']
            rw [@Std.Commutative.comm _ op]
            congr
          . rw [dif_neg nINb]
            have nINb' : ¬ x2.1 ∈ b.support := by
              rw [<- EQ']
              apply nINb
            rw [dif_neg nINb']
            rw [dif_pos INa']
            congr
        . rw [dif_neg nINa]
          have nINa' : ¬ x2.1 ∈ a.support := by
            rw [<- EQ']
            apply nINa
          rcases em (x1.1 ∈ b.support) with INb|nINb
          . rw [dif_pos INb]
            have INb' : x2.1 ∈ b.support := by
              rw [<- EQ']
              apply INb
            rw [dif_pos INb']
            rw [dif_neg nINa']
            congr
          . rw [dif_neg nINb]
            have nINb' : ¬ x2.1 ∈ b.support := by
              rw [<- EQ']
              apply nINb
            rw [dif_neg nINb']
            rw [dif_neg nINa']

-- general version of CFinsupp.binop
def CFinsupp.binop' [DecidableEq A] [DecidableEq B] [Zero B] (op : B → B → B) :
    CFinsupp A B → CFinsupp A B → CFinsupp A B :=
  fun f g =>  ⟨
    (f.1 \ g.1) ∪ (g.1 \ f.1) ∪ {x ∈ f.1 ∩ g.1 | exists (c1: x∈f.1) (c2: x∈g.1), op (f.2 ⟨x,c1⟩) (g.2 ⟨x,c2⟩) ≠ 0},
    fun ⟨x, infg⟩ =>
      if pf: x∈f.1 then
        if pg: x∈g.1 then op (f.2 ⟨x, pf⟩) (g.2 ⟨x, pg⟩)
        else (f.2 ⟨x, pf⟩)
      else
        if pg: x∈g.1 then g.2 ⟨x, pg⟩
        else by
          exfalso; simp at infg
          rcases infg with ⟨_,_⟩ | ⟨_,_⟩ | ⟨_,_,_,_⟩ <;>
          contradiction,
    by
      simp; intro x infg G
      rcases infg with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨_,h1,h2,_⟩ <;>
      simp [h1,h2] at G
      . apply f.nonzero; assumption
      . apply g.nonzero; assumption
      . contradiction
  ⟩

instance CFinsupp.binop'_commutative [DecidableEq A] [DecidableEq B] [Zero B] (op : B → B → B) [Std.Commutative op] : Std.Commutative (@CFinsupp.binop' A _ _ _ _ op) where
  comm := by
    intro a b
    rw [binop', binop']; simp
    constructor
    . apply Finset.ext_iff.mpr
      intro a'
      constructor <;> intro H
      . rw [Finset.mem_union] at H
        rcases H with H1|H1
        . rw [Finset.mem_union]
          apply Or.inr
          rw [Finset.mem_union]
          apply Or.inl
          apply H1
        . rw [Finset.mem_union] at H1
          rcases H1 with H2|H2
          . rw [Finset.mem_union]
            apply Or.inl
            apply H2
          . rw [Finset.mem_union]
            apply Or.inr
            rw [Finset.mem_union]
            apply Or.inr
            have EQ : Finset.filter (fun x ↦ ∃ (c1 : x ∈ a.support) (c2 : x ∈ b.support), ¬op (a.toFun ⟨x, c1⟩) (b.toFun ⟨x, c2⟩) = 0) (a.support ∩ b.support) = Finset.filter (fun x ↦ ∃ (c1 : x ∈ b.support) (c2 : x ∈ a.support), ¬op (b.toFun ⟨x, c1⟩) (a.toFun ⟨x, c2⟩) = 0) (b.support ∩ a.support) := by
              have EQ1 : (a.support ∩ b.support) = (b.support ∩ a.support) := by
                rw [Finset.inter_comm]
              rw [EQ1]
              congr
              ext x
              constructor <;> intro H'
              . obtain ⟨c1, H''⟩ := H'
                obtain ⟨c2, H'''⟩ := H''
                use c2
                use c1
                rw [@Std.Commutative.comm _ op]
                apply H'''
              . obtain ⟨c1, H''⟩ := H'
                obtain ⟨c2, H'''⟩ := H''
                use c2
                use c1
                rw [@Std.Commutative.comm _ op]
                apply H'''
            rw [<- EQ]
            apply H2
      . sorry
    . apply Function.hfunext
      . sorry
      . sorry

instance CFinsupp.DecidableEq [DecidableEq A] [DecidableEq B] [Zero B] : DecidableEq (CFinsupp A B) :=
  fun m₁ m₂ =>
    if c1: m₁.1 = m₂.1 then
      if c2: ∀ x (inOne : x∈ m₁.1), m₁.2 ⟨x,inOne⟩ == m₂.2 ⟨x, by rw [← c1]; exact inOne⟩
      then isTrue (by
        rcases m₁ with ⟨A₁,p₁,nonzero₁⟩; rcases m₂ with ⟨A₂,p₂,nonzero₂⟩
        simp at c1; simp at c2; subst c1; simp
        ext x; rcases x with ⟨x, h⟩
        exact c2 x h)
      else isFalse (by
        by_contra c3
        rcases m₁ with ⟨A₁,p₁,nonzero₁⟩; rcases m₂ with ⟨A₂,p₂,nonzero₂⟩
        simp at c1; subst c1; apply c2; simp
        rcases c3; intros; rfl)
    else isFalse (by
      by_contra c3; rcases c3; contradiction)

instance CFinsuppInstLinearOrder [DecidableEq A] [DecidableEq B] [Zero B] [LinearOrder A] [LinearOrder B] : LinearOrder (CFinsupp A B) where
  le x y := (@Finsupp.Lex.linearOrder A B _ _ _).le (toLex x) (toLex y)
  le_refl := by intros; apply (@Finsupp.Lex.linearOrder A B _ _ _).le_refl
  le_trans := by intros; apply (@Finsupp.Lex.linearOrder A B _ _ _).le_trans <;> assumption
  le_antisymm := by
    intros x y le1 le2;
    rw [← toCFinsupp_ofCFinsupp_inverse x, ← toCFinsupp_ofCFinsupp_inverse y]
    have G: ofCFinsupp.coe x = ofCFinsupp.coe y := by apply (@Finsupp.Lex.linearOrder A B _ _ _).le_antisymm <;> assumption
    rw [G]
  le_total := by intros; apply (@Finsupp.Lex.linearOrder A B _ _ _).le_total
  decidableLE := by intro x y; apply (@Finsupp.Lex.linearOrder A B _ _ _).decidableLE

def CFinsupp.empty A B [Zero B] : CFinsupp A B where
  support := Finset.empty
  toFun := by rintro ⟨x,h⟩; exfalso; apply Finset.not_mem_empty; assumption
  nonzero := by rintro ⟨x,h⟩; exfalso; apply Finset.not_mem_empty; assumption

def CFinsupp_add [DecidableEq A] [Zero B] (self: CFinsupp A B) (key: A) (val: B) (nonzero: val ≠ 0) : CFinsupp A B where
  support := self.support ∪ {key}
  toFun m := if m==key then val else self m
  nonzero := by
    rintro ⟨x,hunion⟩
    rcases em (x==key) with h|h <;> simp [h]
    assumption
    have : x ∈ self.support := by
      rw [Finset.mem_union] at hunion
      rcases hunion with _|h2; assumption
      simp at h2; exfalso; apply h; exact beq_iff_eq.mpr h2
    intro g; apply self.nonzero ⟨x,this⟩;
    rw [CFinsupp.instFunLike] at g; simp at g
    rw [Coe.coe, ofCFinsupp] at g; simp at g
    apply g
