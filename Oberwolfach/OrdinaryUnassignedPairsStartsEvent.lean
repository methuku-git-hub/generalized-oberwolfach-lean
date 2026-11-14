module

public import Oberwolfach.ExpandedUnassignedPairsStarts

@[expose] public section
/-! Named unassigned pair-availability and interval-start tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryUnassignedPairsStartsEvent {V U Color:Type}
    [Fintype V] [Fintype U] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (θ:ℝ) (q:U→Bool→ℝ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Color e):Prop :=
  (∀x y,x≠y→(5/32:ℝ)*θ^2*Fintype.card U-(Fintype.card V:ℝ)^(3/4:ℝ)≤
    rawIntervalUnassignedPairColumnCount π d (fun e=>σ (Sum.inr e)) x y Finset.univ) ∧
  ∀v g,|rawIntervalStartColumnCount π d (fun e=>σ (Sum.inr e)) v g Finset.univ-∑w,q w g/(d:ℝ)|<(Fintype.card V:ℝ)^(3/4:ℝ)
end Oberwolfach
