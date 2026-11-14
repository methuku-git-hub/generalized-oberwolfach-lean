module

public import Oberwolfach.OrdinaryFiniteAttachments

@[expose] public section

/-! The explicit map from an expansion to its attachment graph sends
one distinguished private rim vertex to the selected old endpoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E J I W : Type*}

def attachmentCollapse (z : W) (ρ : I → V) : V ⊕ (I×W) → V ⊕ (I×W)
  | .inl a => .inl a
  | .inr (i,w) => attachmentWheelEmbedding z ρ i w

def expansionAttachmentRoots (x : E → V) (v : J → V) : E ⊕ J → V := Sum.elim x v

theorem attachmentCollapse_private_preimage (z : W) (ρ : I → V)
    (a : V ⊕ (I×W)) (i : I) (w : W) :
    attachmentCollapse z ρ a=.inr (i,w) ↔ a=.inr (i,w) ∧ w≠z := by
  cases a with
  | inl a => simp [attachmentCollapse]
  | inr p =>
    rcases p with ⟨j,w'⟩
    rw [attachmentCollapse,attachmentWheelEmbedding_private]
    simp only [Sum.inr.injEq,Prod.mk.injEq]
    aesop

theorem attachmentCollapse_old_preimage (z : W) (ρ : I → V) (a : V ⊕ (I×W)) (v : V) :
    attachmentCollapse z ρ a=.inl v ↔ a=.inl v ∨ ∃ i,a=.inr (i,z) ∧ ρ i=v := by
  cases a with
  | inl a => simp [attachmentCollapse]
  | inr p =>
    rcases p with ⟨i,w⟩
    rw [attachmentCollapse,attachmentWheelEmbedding_old]
    simp

theorem expansionPrivateAdj_adj (C : SimpleGraph W) (z o : W) (i : E ⊕ J) (a b : W)
    (h : expansionPrivateAdj C z o i a b) : C.Adj a b := by
  cases i with
  | inl e => exact h.1
  | inr j => exact h

theorem ordinaryExpansion_attachment_rim_hom (G : SimpleGraph V) (C : SimpleGraph W) (z o : W)
    (hzo : C.Adj z o) (x y : E → V) (v : J → V) (hG : ∀ e,G.Adj (x e) (y e))
    (a b : ExpansionRow V E J W) (h : (ordinaryExpansionRim C z o x y).Adj a b) :
    (ordinaryAttachmentRim G C z (expansionAttachmentRoots x v)).Adj
      (attachmentCollapse z (expansionAttachmentRoots x v) a)
      (attachmentCollapse z (expansionAttachmentRoots x v) b) := by
  have hcross (a : V) (p : (E ⊕ J) × W) (h : expansionCrossAdj z o x y a p) :
      (ordinaryAttachmentRim G C z (expansionAttachmentRoots x v)).Adj
        (.inl a) (attachmentCollapse z (expansionAttachmentRoots x v) (.inr p)) := by
    rcases p with ⟨i,w⟩
    cases i with
    | inr j => exact h.elim
    | inl e =>
      rcases h with ⟨ha,hw⟩|⟨ha,hw⟩
      · subst a;subst w
        simp [attachmentCollapse,attachmentWheelEmbedding,ordinaryAttachmentRim,expansionAttachmentRoots,hzo.ne.symm,hzo]
      · subst a;subst w
        simpa [attachmentCollapse,attachmentWheelEmbedding,ordinaryAttachmentRim,expansionAttachmentRoots] using (hG e).symm
  cases a with
  | inl a =>
    cases b with
    | inl b => exact h.elim
    | inr p => exact hcross a p h
  | inr p =>
    cases b with
    | inl b => exact (hcross b p h).symm
    | inr q =>
      rcases p with ⟨i,w⟩;rcases q with ⟨j,w'⟩
      obtain ⟨hij,h⟩ := h
      subst j
      have hC := expansionPrivateAdj_adj C z o i w w' h
      by_cases hw : w=z <;> by_cases hw' : w'=z
      · exact (hC.ne (hw.trans hw'.symm)).elim
      · subst w
        simp [attachmentCollapse,attachmentWheelEmbedding,ordinaryAttachmentRim,hw',hC]
      · subst w'
        simp [attachmentCollapse,attachmentWheelEmbedding,ordinaryAttachmentRim,hw,hC.symm]
      · simp [attachmentCollapse,attachmentWheelEmbedding,ordinaryAttachmentRim,hw,hw',hC]

theorem ordinaryExpansion_attachment_spoke_hom (H : V → U → Prop) (z : W)
    (x : E → V) (v : J → V) (u : J → U) (hH : ∀ j,H (v j) (u j))
    (a : ExpansionRow V E J W) (b : ExpansionHub U E J) (h : ordinaryExpansionSpokes z v u a b) :
    ordinaryAttachmentSpokes H z (expansionAttachmentRoots x v)
      (attachmentCollapse z (expansionAttachmentRoots x v) a) b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact h.elim
    | inr i =>
      cases i with
      | inl e => exact h.elim
      | inr j => exact h.symm
  | inr p =>
    rcases p with ⟨i,w⟩
    cases i with
    | inl e =>
      cases b with
      | inl b => exact h.elim
      | inr i =>
        change i=Sum.inl e at h
        subst i
        by_cases hw : w=z <;> simp [attachmentCollapse,attachmentWheelEmbedding,ordinaryAttachmentSpokes,hw]
    | inr j =>
      cases b with
      | inl b =>
        obtain ⟨hw,hb⟩ := h
        subst w;subst b
        simpa [attachmentCollapse,attachmentWheelEmbedding,ordinaryAttachmentSpokes,expansionAttachmentRoots] using hH j
      | inr i =>
        obtain ⟨hw,hi⟩ := h
        subst i
        simp [attachmentCollapse,attachmentWheelEmbedding,ordinaryAttachmentSpokes,hw]

end Oberwolfach
