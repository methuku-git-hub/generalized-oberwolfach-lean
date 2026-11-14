module

public import Oberwolfach.FiniteWeightedPartitionBad

@[expose] public section
/-! The weighted partition with the supported subtype's finite instance
made explicit for large dependent structures. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_weighted_partition_with_bad_explicit {I:Type} [Fintype I]
    (anchor good bad:I→Prop) [Fintype {i // good i}] (w:I→ℝ) (hbad:∀i,¬good i↔bad i):
    (∑i,if anchor i then w i else 0)=
      (∑i:{i // good i},if anchor i.val then w i.val else 0)+
      (∑i,if anchor i ∧ bad i then w i else 0):=by
  have hp:=finite_weighted_partition_with_bad anchor good bad w hbad
  convert hp using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
