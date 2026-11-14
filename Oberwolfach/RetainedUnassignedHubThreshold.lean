module

public import Oberwolfach.RetainedUnassignedHubLocalFamily

@[expose] public section
/-! Choose the hub-row threshold before the host and its size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def retainedUnassignedHubThreshold (d:ℕ) (hd:2≤d) (C δ:ℝ) (hC:0≤C) (hδ:0<δ) : ℕ :=
  Classical.choose (raw_retained_unassigned_hub_local_family_small_failure d hd C δ hC hδ)

theorem retainedUnassignedHubThreshold_positive (d:ℕ) (hd:2≤d) (C δ:ℝ) (hC:0≤C) (hδ:0<δ) :
    1≤retainedUnassignedHubThreshold d hd C δ hC hδ :=
  (Classical.choose_spec (raw_retained_unassigned_hub_local_family_small_failure d hd C δ hC hδ)).1
end Oberwolfach
