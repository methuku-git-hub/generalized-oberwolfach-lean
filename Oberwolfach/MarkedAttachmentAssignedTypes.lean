module

public import Oberwolfach.MarkedAttachmentPairing

@[expose] public section

/-! Put the attachment permutation in the direction used by the wheel
caller: an attachment slot maps to its assigned hub occurrence. The Hall
construction supplies the opposite direction, so its inverse is used.
Rows with no incidences are handled without a nonempty assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 11000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem marked_attachment_assigned_types {X Y S:Type*} [Fintype X] [Fintype Y] [Fintype S]
    (K:Finset X) (SK:Finset S)
    (hXY:Fintype.card X=Fintype.card Y) (hXS:Fintype.card X=Fintype.card S)
    (hK:K.card=SK.card) (hpad:¬(Fintype.card X=1∧K.card=1)):
    ∃ τ:Equiv.Perm (X⊕Y),∃ a:X≃S,∃ d:Y≃S,
      (∀ x,τ x≠x)∧
      (∀ x:X,a x∈SK↔τ (Sum.inl x)∈K.image (Sum.inl (β:=Y)))∧
      ∀ y:Y,τ (Sum.inr y)∉K.image (Sum.inl (β:=Y)):=by
  by_cases hx:0<Fintype.card X
  · obtain ⟨σ,a,d,hσ,_,ha,hd⟩:=marked_attachment_pairings K SK hXY hXS hK hx hpad
    refine ⟨σ.symm,a,d,?_,ha,hd⟩
    intro x he
    have hh:=congrArg σ he
    exact hσ x (by simpa only [Equiv.apply_symm_apply] using hh.symm)
  · have hx0:Fintype.card X=0:=by omega
    have hy0:Fintype.card Y=0:=hXY.symm.trans hx0
    letI:IsEmpty X:=Fintype.card_eq_zero_iff.mp hx0
    letI:IsEmpty Y:=Fintype.card_eq_zero_iff.mp hy0
    refine ⟨Equiv.refl _,Fintype.equivOfCardEq hXS,Fintype.equivOfCardEq (hXY.symm.trans hXS),?_,?_,?_⟩
    · intro x;exact isEmptyElim x
    · intro x;exact isEmptyElim x
    · intro y;exact isEmptyElim y

end Oberwolfach
