module

public import Oberwolfach.RetainedUnassignedColumnLocalFamily

@[expose] public section
/-! Choose the local column threshold before the host and its size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def retainedUnassignedColumnThreshold (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ) : ℕ :=
  Classical.choose (raw_retained_unassigned_column_local_family_small_failure d hd δ hδ)

theorem retainedUnassignedColumnThreshold_positive (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ) :
    1≤retainedUnassignedColumnThreshold d hd δ hδ :=
  (Classical.choose_spec (raw_retained_unassigned_column_local_family_small_failure d hd δ hδ)).1
end Oberwolfach
