module

public import Oberwolfach.OrdinaryInducedWheelWeight
public import Oberwolfach.OrdinaryNonrootWheelRimPartition

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

theorem ordinary_nonroot_weight_rim_identity (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (T:Finset V) (W:Finset U) (w:OrdinaryWheel Q F H r→ℝ):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    ∀x y:A,ordinaryRimLoad w x.val y.val=
      ordinaryRimLoad (ordinaryInducedWheelWeight Q F H A B r w) x y+
      ∑C,if (ordinaryWheelRim C).Adj x.val y.val ∧
        (ordinaryWheelHub C∈W ∨ ∃z∈T,z∈(ordinaryWheelRim C).support) then w C else 0:=by
  intro A B x y
  have hp:=ordinary_nonroot_wheel_rim_partition Q F H r T W w x.val y.val
  have hi:=ordinary_induced_weight_rim_identity Q F H A B r w x y
  rw [hi]
  unfold ordinaryRimLoad
  convert hp using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _

end Oberwolfach
