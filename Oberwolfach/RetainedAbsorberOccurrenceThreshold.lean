module

public import Oberwolfach.RetainedAbsorberOccurrenceLocalFamily

@[expose] public section
/-! Choose the local column threshold before the host and its size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def retainedAbsorberOccurrenceThreshold (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ) : ℕ :=
  Classical.choose (raw_retained_absorber_occurrence_local_small_failure d hd δ hδ)

theorem retainedAbsorberOccurrenceThreshold_positive (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ) :
    1≤retainedAbsorberOccurrenceThreshold d hd δ hδ :=
  (Classical.choose_spec (raw_retained_absorber_occurrence_local_small_failure d hd δ hδ)).1
end Oberwolfach
