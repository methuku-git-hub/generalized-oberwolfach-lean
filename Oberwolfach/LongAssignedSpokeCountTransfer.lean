module

public import Oberwolfach.LongRawHubSpokeColumnBridge
public import Oberwolfach.LongAssignedSamplingRecipe

@[expose] public section
/-! Transfer the original assigned ordinary spoke-column event to the
hub-root count hypothesis required by the retained matching tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance countTransferFinDecidable (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_spoke_column_to_hub_root_counts
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (g:Bool) (t:ℝ)
    (h:∀u,|rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) g true false u Finset.univ-
      longAssignedSpokeProbability F hF K m θ u true*(n:ℝ)|<t):
    ∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun z=>
      longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (σ e)) g true z=true)).card:ℝ)-
        longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤t :=by
  intro u
  rw [long_raw_ordinary_hub_roots_eq_spoke_column]
  exact (by simpa [longAssignedSpokeProbability] using h u : _ < t).le
end Oberwolfach
