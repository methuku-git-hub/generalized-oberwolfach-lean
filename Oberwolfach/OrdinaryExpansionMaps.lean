module

public import Oberwolfach.OrdinaryFiniteExpansion

@[expose] public section

/-! Collapsing original vertices in an expansion preserves every edge
with multiplicity one. The private wheel indices are never collapsed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V V' U U' E J W : Type*}

def expansionRowMap (f : V → V') : ExpansionRow V E J W → ExpansionRow V' E J W := Sum.map f id

def expansionHubMap (g : U → U') : ExpansionHub U E J → ExpansionHub U' E J := Sum.map g id

theorem expansionCrossAdj_unique (z o : W) (hzo : z≠o) (x y : E → V)
    (p : (E ⊕ J) × W) (a b : V)
    (ha : expansionCrossAdj z o x y a p) (hb : expansionCrossAdj z o x y b p) : a=b := by
  rcases p with ⟨i,w⟩
  cases i with
  | inr j => exact ha.elim
  | inl e =>
    rcases ha with ⟨ha,hw⟩|⟨ha,hw⟩ <;> rcases hb with ⟨hb,hw'⟩|⟨hb,hw'⟩
    · exact ha.trans hb.symm
    · exact (hzo (hw'.symm.trans hw)).elim
    · exact (hzo (hw.symm.trans hw')).elim
    · exact ha.trans hb.symm

theorem ordinaryExpansion_rim_hom (C : SimpleGraph W) (z o : W) (x y : E → V) (f : V → V')
    (a b : ExpansionRow V E J W) (h : (ordinaryExpansionRim C z o x y).Adj a b) :
    (ordinaryExpansionRim C z o (f ∘ x) (f ∘ y)).Adj (expansionRowMap f a) (expansionRowMap f b) := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact h.elim
    | inr p =>
      rcases p with ⟨i,w⟩
      cases i with
      | inr j => exact h.elim
      | inl e =>
        rcases h with ⟨rfl,hw⟩|⟨rfl,hw⟩
        · exact Or.inl ⟨rfl,hw⟩
        · exact Or.inr ⟨rfl,hw⟩
  | inr p =>
    cases b with
    | inl b =>
      rcases p with ⟨i,w⟩
      cases i with
      | inr j => exact h.elim
      | inl e =>
        rcases h with ⟨rfl,hw⟩|⟨rfl,hw⟩
        · exact Or.inl ⟨rfl,hw⟩
        · exact Or.inr ⟨rfl,hw⟩
    | inr q => exact h

theorem ordinaryExpansion_rim_preimage (C : SimpleGraph W) (z o : W) (x y : E → V) (f : V → V')
    (a b : ExpansionRow V' E J W) (h : (ordinaryExpansionRim C z o (f ∘ x) (f ∘ y)).Adj a b) :
    ∃ a' b',(ordinaryExpansionRim C z o x y).Adj a' b' ∧ expansionRowMap f a'=a ∧ expansionRowMap f b'=b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact h.elim
    | inr p =>
      rcases p with ⟨i,w⟩
      cases i with
      | inr j => exact h.elim
      | inl e =>
        rcases h with ⟨rfl,hw⟩|⟨rfl,hw⟩
        · exact ⟨.inl (x e),.inr (.inl e,w),Or.inl ⟨rfl,hw⟩,rfl,rfl⟩
        · exact ⟨.inl (y e),.inr (.inl e,w),Or.inr ⟨rfl,hw⟩,rfl,rfl⟩
  | inr p =>
    cases b with
    | inl b =>
      rcases p with ⟨i,w⟩
      cases i with
      | inr j => exact h.elim
      | inl e =>
        rcases h with ⟨rfl,hw⟩|⟨rfl,hw⟩
        · exact ⟨.inr (.inl e,w),.inl (x e),Or.inl ⟨rfl,hw⟩,rfl,rfl⟩
        · exact ⟨.inr (.inl e,w),.inl (y e),Or.inr ⟨rfl,hw⟩,rfl,rfl⟩
    | inr q => exact ⟨.inr p,.inr q,h,rfl,rfl⟩

theorem ordinaryExpansion_rim_dart_injective (C : SimpleGraph W) (z o : W) (hzo : z≠o)
    (x y : E → V) (f : V → V') (a b c d : ExpansionRow V E J W)
    (hab : (ordinaryExpansionRim C z o x y).Adj a b)
    (hcd : (ordinaryExpansionRim C z o x y).Adj c d)
    (hac : expansionRowMap f a=expansionRowMap f c) (hbd : expansionRowMap f b=expansionRowMap f d) :
    a=c ∧ b=d := by
  cases a with
  | inl a =>
    cases c with
    | inr p => cases hac
    | inl c =>
      cases b with
      | inl b => exact hab.elim
      | inr p =>
        cases d with
        | inl d => cases hbd
        | inr q =>
          have hpq : p=q := Sum.inr.inj hbd
          subst q
          exact ⟨congrArg Sum.inl (expansionCrossAdj_unique z o hzo x y p a c hab hcd),rfl⟩
  | inr p =>
    cases c with
    | inl c => cases hac
    | inr q =>
      have hpq : p=q := Sum.inr.inj hac
      subst q
      cases b with
      | inl b =>
        cases d with
        | inr q => cases hbd
        | inl d =>
          exact ⟨rfl,congrArg Sum.inl (expansionCrossAdj_unique z o hzo x y p b d hab hcd)⟩
      | inr q =>
        cases d with
        | inl d => cases hbd
        | inr s => exact ⟨rfl,congrArg Sum.inr (Sum.inr.inj hbd)⟩

theorem ordinaryExpansion_rim_edge_injective (C : SimpleGraph W) (z o : W) (hzo : z≠o)
    (x y : E → V) (f : V → V') :
    Set.InjOn (Sym2.map (expansionRowMap (E:=E) (J:=J) (W:=W) f))
      (ordinaryExpansionRim C z o x y).edgeSet := by
  intro e he e' he' hh
  induction e using Sym2.ind with
  | _ a b =>
    induction e' using Sym2.ind with
    | _ c d =>
      change (ordinaryExpansionRim C z o x y).Adj a b at he
      change (ordinaryExpansionRim C z o x y).Adj c d at he'
      rcases Sym2.eq_iff.mp hh with ⟨hac,hbd⟩|⟨had,hbc⟩
      · obtain ⟨rfl,rfl⟩ := ordinaryExpansion_rim_dart_injective C z o hzo x y f a b c d he he' hac hbd
        rfl
      · obtain ⟨rfl,rfl⟩ := ordinaryExpansion_rim_dart_injective C z o hzo x y f a b d c he he'.symm had hbc
        exact Sym2.eq_swap

theorem ordinaryExpansion_rim_map_eq (C : SimpleGraph W) (z o : W)
    (x y : E → V) (f : V → V') :
    (ordinaryExpansionRim (J:=J) C z o x y).map (expansionRowMap f)=
      ordinaryExpansionRim C z o (f ∘ x) (f ∘ y) := by
  ext a b
  rw [SimpleGraph.map_adj']
  constructor
  · rintro ⟨_,a',b',h,rfl,rfl⟩
    exact ordinaryExpansion_rim_hom C z o x y f a' b' h
  · intro h
    obtain ⟨a',b',hab,ha,hb⟩ := ordinaryExpansion_rim_preimage C z o x y f a b h
    exact ⟨h.ne,a',b',hab,ha,hb⟩

end Oberwolfach
