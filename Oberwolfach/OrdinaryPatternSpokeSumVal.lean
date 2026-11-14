module

public import Oberwolfach.OrdinaryPatternSpokeIndicator

@[expose] public section
/-! Root-omitted spoke load as a sum over admissible wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U] {r:ℕ}
theorem ordinary_pattern_spoke_sum_val (P Q F:SimpleGraph V) (H:V→U→Prop)
    (weight:OrdinaryCycle P r→ℝ) (D:ℝ) (v:V) (u:U):
    resourcePatternLoad ordinaryWheelResources (ordinaryCycleWheelWeight P F r weight D)
      (fun _ _=>true) (Sum.inr (v,u)) (ordinaryResourceState Q H)=
    ∑ W:OrdinaryWheel P F (fun _ :V=>fun _ :U=>True) r,
      if W.val.2=u ∧ v∈(W.val.1.val.val).support ∧ W.val.1.val.val≤Q ∧
        (∀ z∈(W.val.1.val.val).support,z≠v→H z u) then weight W.val.1/D else 0 := by
  apply resource_pattern_indicator_sum ordinaryWheelResources (ordinaryCycleWheelWeight P F r weight D)
    (fun _ _=>true) (Sum.inr (v,u)) (ordinaryResourceState Q H)
    (fun W=>W.val.2=u ∧ v∈(W.val.1.val.val).support ∧ W.val.1.val.val≤Q ∧
        (∀ z∈(W.val.1.val.val).support,z≠v→H z u))
  intro W
  exact ordinary_spoke_pattern_predicate P Q F H v u W
end Oberwolfach
