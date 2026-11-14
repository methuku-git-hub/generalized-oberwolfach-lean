module

public import Oberwolfach.OrdinaryMatchingCorrectedGlobalLocalColours
public import Oberwolfach.RawReservedSpokeList

@[expose] public section

/-! The actual selected reference spokes are exactly the reserved labels
used by the matching and local target estimate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_selected_reference_reserved_labels
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e) (v:V) (w:U):
    rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false v w ↔
      v∈rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w :=by
  simp [rawWheelSpokes,rawReservedSpokeList,rawIntervalOrdinaryOuter,expandedOrdinarySelectedCollapse]
end Oberwolfach
