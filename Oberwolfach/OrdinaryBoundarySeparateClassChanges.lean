module

public import Oberwolfach.OrdinaryBoundaryFactorClassesAfterPacking
public import Oberwolfach.OrdinaryRestrictedChanges

@[expose] public section
/-! A physical boundary-class change bounds the two typed class changes
    separately, without charging a second error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_separate_class_changes
    (A A':Finset V) (B B':Finset U) (f:V⊕U→Prop):
    ((changed (A'.image (Sum.inl:V→V⊕U)) ((A.image Sum.inl).filter f)).card ≤
      (changed (A'.image Sum.inl∪B'.image Sum.inr) ((A.image Sum.inl∪B.image Sum.inr).filter f)).card) ∧
    ((changed (B'.image (Sum.inr:U→V⊕U)) ((B.image Sum.inr).filter f)).card ≤
      (changed (A'.image Sum.inl∪B'.image Sum.inr) ((A.image Sum.inl∪B.image Sum.inr).filter f)).card):=by
  let Left:Finset (V⊕U):=Finset.univ.image Sum.inl
  let Right:Finset (V⊕U):=Finset.univ.image Sum.inr
  have hL1:Left∩(A'.image Sum.inl∪B'.image Sum.inr)=A'.image Sum.inl:=by
    ext z;cases z <;> simp [Left]
  have hL2:Left∩((A.image Sum.inl∪B.image Sum.inr).filter f)=(A.image Sum.inl).filter f:=by
    ext z;cases z <;> simp [Left]
  have hR1:Right∩(A'.image Sum.inl∪B'.image Sum.inr)=B'.image Sum.inr:=by
    ext z;cases z <;> simp [Right]
  have hR2:Right∩((A.image Sum.inl∪B.image Sum.inr).filter f)=(B.image Sum.inr).filter f:=by
    ext z;cases z <;> simp [Right]
  constructor
  · have hh:=changed_inter_card_le Left (A'.image Sum.inl∪B'.image Sum.inr)
      ((A.image Sum.inl∪B.image Sum.inr).filter f)
    rw [hL1,hL2] at hh
    exact hh
  · have hh:=changed_inter_card_le Right (A'.image Sum.inl∪B'.image Sum.inr)
      ((A.image Sum.inl∪B.image Sum.inr).filter f)
    rw [hR1,hR2] at hh
    exact hh
end Oberwolfach
