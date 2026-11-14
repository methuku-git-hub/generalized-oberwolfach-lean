module

public import Oberwolfach.LongActualCorrectionAssignedEventOrientationMatching

@[expose] public section

/-! Choose the protected-class edit tolerance before the later absorber size,
with room for both the correction and orientation in the early deletion budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_correction_class_orientation_budget
    (α ρ₀ c ζEarly ζCorr:ℝ) (hα:0<α) (hρ:0<ρ₀)
    (hc:0<c) (hζ:0<ζEarly) (hCorr:ζCorr≤ζEarly/2) :
    ∃ ξClass:ℝ, 0<ξClass ∧
      ξClass≤min (min (c/4) ((ζEarly/4)/16)) (α*(ρ₀/200)^2/4) ∧
      ζCorr+ξClass+ζEarly/4≤ζEarly := by
  let cap:ℝ:=min (min (c/4) (ζEarly/64)) (α*(ρ₀/200)^2/4)
  have hcap:0<cap:=by dsimp [cap]; positivity
  have hc1:cap≤c/4:=le_trans (min_le_left _ _) (min_le_left _ _)
  have hc2:cap≤ζEarly/64:=le_trans (min_le_left _ _) (min_le_right _ _)
  have hc3:cap≤α*(ρ₀/200)^2/4:=min_le_right _ _
  refine ⟨cap/2,by positivity,?_,?_⟩
  · apply le_min
    · apply le_min <;> linarith
    · linarith
  · linarith
end Oberwolfach
