module

public import Oberwolfach.OrdinaryPatternSpokeSumVal
public import Oberwolfach.OrdinarySpokeIndicatorLocalMixed

@[expose] public section
/-! The omitted-spoke pattern load equals the local cycle potential. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U] {r:ℕ}
theorem ordinary_pattern_spoke_eq_local_bridge (P Q F:SimpleGraph V) (H:V→U→Prop)
    (weight:OrdinaryCycle P r→ℝ) (D:ℝ) (v:V) (u:U):
    resourcePatternLoad ordinaryWheelResources (ordinaryCycleWheelWeight P F r weight D)
      (fun _ _=>true) (Sum.inr (v,u)) (ordinaryResourceState Q H)=
      ordinaryLocalPotential P Q F (Finset.univ.filter (fun z=>H z u)) (fun C=>weight C/D) v := by
  calc
    _ = ∑ W:OrdinaryWheel P F (fun _ :V=>fun _ :U=>True) r,
      if W.val.2=u ∧ v∈(W.val.1.val.val).support ∧ W.val.1.val.val≤Q ∧
        (∀ z∈(W.val.1.val.val).support,z≠v→H z u) then weight W.val.1/D else 0 :=
          ordinary_pattern_spoke_sum_val P Q F H weight D v u
    _ = _ := ordinary_spoke_indicator_sum_eq_local_mixed P Q F H weight D v u
end Oberwolfach
