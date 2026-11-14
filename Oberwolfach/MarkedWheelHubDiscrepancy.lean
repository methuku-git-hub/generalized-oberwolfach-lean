module

public import Oberwolfach.MarkedMixedHubDiscrepancy
public import Oberwolfach.MarkedWheelFiniteBalance

@[expose] public section
/-! A reference marked wheel has zero signed hub discrepancy at every hub. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T]
    {tail head:E→V} {ktail khead:T→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_wheel_hub_discrepancy_zero
    (hH:∀v u,¬(H₀ v u∧HK v u))
    (W:MarkedWheel tail head ktail khead m π b H₀ HK) (u:U):
    markedFiniteHubDiscrepancy HK m (markedWheelSpokePairs W) u=0 := by
  exact marked_finite_hub_discrepancy_of_divisible tail head ktail khead HK m
    (markedWheelArcs W) (markedWheelSpokePairs W) (markedWheel_finite_divisible hH W) u
end Oberwolfach
