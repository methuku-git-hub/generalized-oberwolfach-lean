module

public import Oberwolfach.OrdinaryUnreservedAfterRootCover
public import Oberwolfach.OrdinaryDeepRootFreeFamilies

@[expose] public section
/-! Every wheel in the unreserved host after root covering avoids all deeper
roots, so the later packing itself cannot use their physical stars. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]

theorem ordinary_unreserved_wheels_root_free
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (hr:0<r) (η ell:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z) (A:OrdinaryRootCoverData Q F H X T Z W r η ell)
    (R:SimpleGraph (V⊕U)):
    let Q':=Q\A.rim;let H':=fun v u=>H v u∧¬A.spokes v u;
    ∀C:I→OrdinaryWheel (ordinaryUnreservedRim Q' X R) F (ordinaryUnreservedSpokes H' X Z R) r,
    Disjoint (ordinaryPhysicalGraph (wheelFamilyRim C) (wheelFamilySpokes C)) (ordinaryDeepRootStar T W):=by
  intro Q' H' C
  have hnone:=ordinary_unreserved_after_root_cover Q F H X T Z W r η ell hTX hWZ A R
  apply ordinary_root_free_wheel_family _ F _ r T W C
  · intro i v hv hvT
    obtain ⟨w,hw⟩:=hv
    exact hnone.1 v hvT w ((C i).val.1.property hw)
  · intro i hhub
    have hc:((ordinaryWheelRim (C i)).support.toFinset.card)=r:=(C i).val.1.val.property.support_card
    have hp:0<((ordinaryWheelRim (C i)).support.toFinset.card):=by rw [hc];exact hr
    obtain ⟨v,hv⟩:=Finset.card_pos.mp hp
    have hv':v∈(ordinaryWheelRim (C i)).support:=by simpa using hv
    exact hnone.2.2 (ordinaryWheelHub (C i)) hhub v ((C i).property.1 v hv')
end Oberwolfach
