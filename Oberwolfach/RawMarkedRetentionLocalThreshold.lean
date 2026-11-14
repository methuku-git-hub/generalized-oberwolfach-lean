module

public import Oberwolfach.RawMarkedRetentionLocalEvent

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def rawMarkedLocalRetentionThreshold (d:ℕ) (hd:2≤d) (p ζ c δ:ℝ)
    (hp:0<p) (hζ:0<ζ) (hc:0<c) (hδ:0<δ):ℕ:=
  Classical.choose (raw_marked_retention_local_event d hd p ζ c δ hp hζ hc hδ)

def rawMarkedLocalRetentionAmbientThreshold (d:ℕ) (hd:2≤d) (p ζ c δ:ℝ)
    (hp:0<p) (hζ:0<ζ) (hc:0<c) (hδ:0<δ):ℕ:=
  Classical.choose (Classical.choose_spec (raw_marked_retention_local_event d hd p ζ c δ hp hζ hc hδ))

theorem rawMarkedLocalRetentionThreshold_positive (d:ℕ) (hd:2≤d) (p ζ c δ:ℝ)
    (hp:0<p) (hζ:0<ζ) (hc:0<c) (hδ:0<δ):
    1≤rawMarkedLocalRetentionThreshold d hd p ζ c δ hp hζ hc hδ:=
  (Classical.choose_spec (Classical.choose_spec (raw_marked_retention_local_event d hd p ζ c δ hp hζ hc hδ))).1
end Oberwolfach
