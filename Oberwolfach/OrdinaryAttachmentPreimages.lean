module

public import Oberwolfach.OrdinaryExpansionAttachmentHom

@[expose] public section

/-! Every old edge and every attached-wheel edge is the image of an
explicit expansion edge. No edge-surjectivity assumption is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E J W : Type*}

theorem ordinaryExpansion_attachment_rim_preimage
    (G : SimpleGraph V) (C : SimpleGraph W) (z o : W) (x y : E → V) (v : J → V)
    (hG : ∀ a b,G.Adj a b → ∃ e,s(x e,y e)=s(a,b))
    (a b : ExpansionRow V E J W)
    (h : (ordinaryAttachmentRim G C z (expansionAttachmentRoots x v)).Adj a b) :
    ∃ a' b',(ordinaryExpansionRim C z o x y).Adj a' b' ∧
      attachmentCollapse z (expansionAttachmentRoots x v) a'=a ∧
      attachmentCollapse z (expansionAttachmentRoots x v) b'=b := by
  have hcross (a : V) (i : E ⊕ J) (w : W)
      (h : expansionAttachmentRoots x v i=a ∧ w≠z ∧ C.Adj z w) :
      ∃ a' b',(ordinaryExpansionRim C z o x y).Adj a' b' ∧
        attachmentCollapse z (expansionAttachmentRoots x v) a'=.inl a ∧
        attachmentCollapse z (expansionAttachmentRoots x v) b'=.inr (i,w) := by
    cases i with
    | inl e =>
      by_cases hwo : w=o
      · subst w
        refine ⟨.inl (x e),.inr (.inl e,o),Or.inl ⟨rfl,rfl⟩,?_,?_⟩
        · exact congrArg (Sum.inl (β:=(E⊕J)×W)) h.1
        · simp [attachmentCollapse,attachmentWheelEmbedding,h.2.1]
      · refine ⟨.inr (.inl e,z),.inr (.inl e,w),⟨rfl,h.2.2,?_⟩,?_,?_⟩
        · simp [hwo,h.2.1]
        · simpa [attachmentCollapse,attachmentWheelEmbedding,expansionAttachmentRoots] using congrArg (Sum.inl (β:=(E⊕J)×W)) h.1
        · simp [attachmentCollapse,attachmentWheelEmbedding,h.2.1]
    | inr j =>
      refine ⟨.inr (.inr j,z),.inr (.inr j,w),⟨rfl,h.2.2⟩,?_,?_⟩
      · simpa [attachmentCollapse,attachmentWheelEmbedding,expansionAttachmentRoots] using congrArg (Sum.inl (β:=(E⊕J)×W)) h.1
      · simp [attachmentCollapse,attachmentWheelEmbedding,h.2.1]
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      obtain ⟨e,he⟩ := hG a b h
      rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩|⟨hb,ha⟩
      · refine ⟨.inr (.inl e,z),.inl (y e),Or.inr ⟨rfl,rfl⟩,?_,?_⟩
        · simp [attachmentCollapse,attachmentWheelEmbedding,expansionAttachmentRoots,ha]
        · exact congrArg (Sum.inl (β:=(E⊕J)×W)) hb
      · refine ⟨.inl (y e),.inr (.inl e,z),Or.inr ⟨rfl,rfl⟩,?_,?_⟩
        · exact congrArg (Sum.inl (β:=(E⊕J)×W)) ha
        · simp [attachmentCollapse,attachmentWheelEmbedding,expansionAttachmentRoots,hb]
    | inr p => exact hcross a p.1 p.2 h
  | inr p =>
    cases b with
    | inl b =>
      obtain ⟨a',b',hab,ha,hb⟩ := hcross b p.1 p.2 h
      exact ⟨b',a',hab.symm,hb,ha⟩
    | inr q =>
      rcases p with ⟨i,w⟩;rcases q with ⟨j,w'⟩
      obtain ⟨hij,hw,hw',hC⟩ := h
      subst j
      refine ⟨.inr (i,w),.inr (i,w'),⟨rfl,?_⟩,?_,?_⟩
      · cases i with
        | inl e => exact ⟨hC,by simp [hw,hw']⟩
        | inr j => exact hC
      · simp [attachmentCollapse,attachmentWheelEmbedding,hw]
      · simp [attachmentCollapse,attachmentWheelEmbedding,hw']

theorem ordinaryExpansion_attachment_spoke_preimage
    (H : V → U → Prop) (z : W) (x : E → V) (v : J → V) (u : J → U)
    (hH : ∀ a b,H a b → ∃ j,v j=a ∧ u j=b)
    (a : ExpansionRow V E J W) (b : ExpansionHub U E J)
    (h : ordinaryAttachmentSpokes H z (expansionAttachmentRoots x v) a b) :
    ∃ a',ordinaryExpansionSpokes z v u a' b ∧
      attachmentCollapse z (expansionAttachmentRoots x v) a'=a := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      obtain ⟨j,hv,hu⟩ := hH a b h
      refine ⟨.inr (.inr j,z),⟨rfl,hu.symm⟩,?_⟩
      simp [attachmentCollapse,attachmentWheelEmbedding,expansionAttachmentRoots,hv]
    | inr i =>
      cases i with
      | inl e =>
        refine ⟨.inr (.inl e,z),rfl,?_⟩
        simpa [attachmentCollapse,attachmentWheelEmbedding,expansionAttachmentRoots] using congrArg (Sum.inl (β:=(E⊕J)×W)) h
      | inr j => exact ⟨.inl (v j),rfl,congrArg (Sum.inl (β:=(E⊕J)×W)) h⟩
  | inr p =>
    rcases p with ⟨i,w⟩
    cases b with
    | inl b => exact h.elim
    | inr j =>
      obtain ⟨hw,hij⟩ := h
      subst j
      refine ⟨.inr (i,w),?_,by simp [attachmentCollapse,attachmentWheelEmbedding,hw]⟩
      cases i with
      | inl e => rfl
      | inr j => exact ⟨hw,rfl⟩

end Oberwolfach
