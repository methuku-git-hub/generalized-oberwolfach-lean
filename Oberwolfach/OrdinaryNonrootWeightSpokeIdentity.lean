module

public import Oberwolfach.OrdinaryInducedWheelWeight
public import Oberwolfach.OrdinaryNonrootWheelSpokePartition

@[expose] public section
/-! Exact parent = induced + excluded wheel-load identities on the same
sample, for rim and spoke edges in adaptive nonroot domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_weight_spoke_identity (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (T:Finset V) (W:Finset U) (w:OrdinaryWheel Q F H r→ℝ):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    ∀(v:A) (u:B),ordinarySpokeLoad w v.val u.val=
      ordinarySpokeLoad (ordinaryInducedWheelWeight Q F H A B r w) v u+
      ∑C,if (ordinaryWheelHub C=u.val ∧ v.val∈(ordinaryWheelRim C).support) ∧
        (ordinaryWheelHub C∈W ∨ ∃z∈T,z∈(ordinaryWheelRim C).support) then w C else 0:=by
  intro A B v u
  have hp:=ordinary_nonroot_wheel_spoke_partition Q F H r T W w v.val u.val
  have hi:=ordinary_induced_weight_spoke_identity Q F H A B r w v u
  rw [hi]
  unfold ordinarySpokeLoad
  convert hp using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
