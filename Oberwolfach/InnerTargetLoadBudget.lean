module

public import Oberwolfach.InnerTargetHostOrderBounds

@[expose] public section
/-! The target occurrence load fits the original small residual parameter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem inner_target_occurrence_budget
    (θ δ η ζ ρ:ℝ) (hθ:0≤θ) (hθδ:10*θ≤δ)
    (hη:η≤θ/4096) (hζ:ζ≤θ/4096) (hρ:ρ≤θ/4096):
    2*θ+η+ζ+ρ≤δ/4:=by
  linarith
end Oberwolfach
