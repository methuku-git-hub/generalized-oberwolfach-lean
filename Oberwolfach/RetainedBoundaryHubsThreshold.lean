module

public import Oberwolfach.RetainedBoundaryHubsLocalFamily

@[expose] public section
/-! Choose the local column threshold before the host and its size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def retainedBoundaryHubsThreshold (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ) : ℕ :=
  Classical.choose (raw_retained_boundary_hubs_local_small_failure d hd δ hδ)

theorem retainedBoundaryHubsThreshold_positive (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ) :
    1≤retainedBoundaryHubsThreshold d hd δ hδ :=
  (Classical.choose_spec (raw_retained_boundary_hubs_local_small_failure d hd δ hδ)).1
end Oberwolfach
