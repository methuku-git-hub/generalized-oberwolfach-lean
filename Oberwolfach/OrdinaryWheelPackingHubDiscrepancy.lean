module

public import Oberwolfach.OrdinaryWheelHubDiscrepancy

@[expose] public section
/-! The exact contribution of disjoint ordinary wheels may use a different
length for each wheel. -/
set_option autoImplicit false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U] [DecidableEq I]

theorem ordinary_wheel_packing_unmarked_hub_discrepancy
    (π:Equiv.Perm V) (b m:ℕ) (HK:V→U→Prop) (M:Finset I) (ℓ:I→ℕ)
    (W:∀i,OrderedOrdinaryWheel (U:=U) π b (ℓ i))
    (hHK:∀i∈M,∀j,¬HK ((W i).1.val j) (W i).2)
    (hdis:∀i∈M,∀j∈M,i≠j→Disjoint (ordinaryWheelSpokePairs (W i)) (ordinaryWheelSpokePairs (W j)))
    (u:U):
    markedFiniteHubDiscrepancy HK m (M.biUnion (fun i=>ordinaryWheelSpokePairs (W i))) u =
      ∑i∈M,if u=(W i).2 then (ℓ i:ℤ) else 0 := by
  rw [marked_finite_hub_discrepancy_biUnion HK m M (fun i=>ordinaryWheelSpokePairs (W i)) hdis u]
  apply Finset.sum_congr rfl
  intro i hi
  exact ordinary_wheel_unmarked_hub_discrepancy HK m (W i) (hHK i hi) u
end Oberwolfach
