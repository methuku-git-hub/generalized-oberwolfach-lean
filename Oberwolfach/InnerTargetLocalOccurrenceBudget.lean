module

public import Oberwolfach.InnerTargetLoadBudget

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem inner_target_local_occurrence_budget
    (A H:ℕ) (θ δ η ζ ρ e z:ℝ)
    (hθ:0≤θ) (hθδ:10*θ≤δ) (hη:η≤θ/4096) (hζ:ζ≤θ/4096) (hρ:ρ≤θ/4096)
    (hH:(H:ℝ)≤A) (hζη:0≤ζ) (he:e≤η*A) (hz:z≤ρ*A):
    2*θ*H+e+ζ*H+z≤δ*A/4:=by
  have hcoef:=inner_target_occurrence_budget θ δ η ζ ρ hθ hθδ hη hζ hρ
  have hA:(0:ℝ)≤A:=Nat.cast_nonneg A
  have hθH:=mul_le_mul_of_nonneg_left hH (show 0≤2*θ by positivity)
  have hζH:=mul_le_mul_of_nonneg_left hH hζη
  have hh:=mul_le_mul_of_nonneg_right hcoef hA
  nlinarith only [hθH,hζH,he,hz,hh]
end Oberwolfach
