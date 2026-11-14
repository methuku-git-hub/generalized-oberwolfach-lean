module

public import Oberwolfach.FiniteWeightedPartition

@[expose] public section
/-! A supported/excluded weighted partition with an equivalent explicit bad
predicate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_weighted_partition_with_bad {I:Type} [Fintype I]
    (anchor good bad:I→Prop) (w:I→ℝ) (hbad:∀i,¬good i↔bad i):
    (∑i,if anchor i then w i else 0)=
      (∑i:{i // good i},if anchor i.val then w i.val else 0)+
      (∑i,if anchor i ∧ bad i then w i else 0):=by
  have hp:=finite_weighted_supported_partition anchor good w
  simp only [hbad] at hp
  convert hp using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
