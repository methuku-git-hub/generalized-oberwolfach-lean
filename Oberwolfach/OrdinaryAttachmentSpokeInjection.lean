module

public import Oberwolfach.OrdinaryExpansionAttachmentHom

@[expose] public section

/-! The attachment identification is injective on spokes when the
original spoke identifiers encode distinct ordered row/hub pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E J W : Type*}

theorem ordinaryExpansion_attachment_spoke_row_injective
    (z : W) (x : E → V) (v : J → V) (u : J → U)
    (hvu : Function.Injective (fun j => (v j,u j)))
    (a c : ExpansionRow V E J W) (b : ExpansionHub U E J)
    (ha : ordinaryExpansionSpokes z v u a b) (hc : ordinaryExpansionSpokes z v u c b)
    (heq : attachmentCollapse z (expansionAttachmentRoots x v) a=
      attachmentCollapse z (expansionAttachmentRoots x v) c) : a=c := by
  cases b with
  | inl b =>
    cases a with
    | inl a => exact ha.elim
    | inr p =>
      rcases p with ⟨i,w⟩
      cases i with
      | inl e => exact ha.elim
      | inr j =>
        cases c with
        | inl c => exact hc.elim
        | inr q =>
          rcases q with ⟨i',w'⟩
          cases i' with
          | inl e => exact hc.elim
          | inr j' =>
            obtain ⟨hw,hu⟩ := ha;obtain ⟨hw',hu'⟩ := hc
            subst w;subst w'
            have hv : v j=v j' := by
              simpa [attachmentCollapse,attachmentWheelEmbedding,expansionAttachmentRoots] using heq
            have hjj : j=j' := hvu (Prod.ext hv (hu.symm.trans hu'))
            subst j';rfl
  | inr k =>
    have hindex (i : E ⊕ J) (w : W) (h : ordinaryExpansionSpokes z v u (.inr (i,w)) (.inr k)) : i=k := by
      cases i with
      | inl e => exact h.symm
      | inr j => exact h.2.symm
    have hmix (a : V) (i : E ⊕ J) (w : W)
        (ha : ordinaryExpansionSpokes z v u (.inl a) (.inr k))
        (hc : ordinaryExpansionSpokes z v u (.inr (i,w)) (.inr k))
        (heq : attachmentCollapse z (expansionAttachmentRoots x v) (.inl a)=
          attachmentCollapse z (expansionAttachmentRoots x v) (.inr (i,w))) : False := by
      have hw := ((attachmentWheelEmbedding_old z (expansionAttachmentRoots x v) i w a).mp heq.symm).1
      have hik := hindex i w hc
      subst k
      cases i with
      | inl e => exact ha.elim
      | inr j => exact hc.1 hw
    cases a with
    | inl a =>
      cases c with
      | inl c => exact congrArg Sum.inl (Sum.inl.inj heq)
      | inr p => exact (hmix a p.1 p.2 ha hc heq).elim
    | inr p =>
      cases c with
      | inl c => exact (hmix c p.1 p.2 hc ha heq.symm).elim
      | inr q =>
        rcases p with ⟨i,w⟩;rcases q with ⟨j,w'⟩
        have hik := hindex i w ha
        have hjk := hindex j w' hc
        subst i;subst j
        have hww := (attachmentWheelEmbedding z (expansionAttachmentRoots x v) k).injective heq
        subst w';rfl

theorem ordinaryExpansion_attachment_spoke_injective
    (z : W) (x : E → V) (v : J → V) (u : J → U)
    (hvu : Function.Injective (fun j => (v j,u j))) :
    Set.InjOn (Prod.map (attachmentCollapse z (expansionAttachmentRoots x v)) id)
      {e | ordinaryExpansionSpokes z v u e.1 e.2} := by
  rintro ⟨a,b⟩ ha ⟨c,d⟩ hc heq
  have hbd : b=d := congrArg Prod.snd heq
  subst d
  have hac := ordinaryExpansion_attachment_spoke_row_injective z x v u hvu a c b ha hc
    (congrArg Prod.fst heq)
  subst c;rfl

end Oberwolfach
