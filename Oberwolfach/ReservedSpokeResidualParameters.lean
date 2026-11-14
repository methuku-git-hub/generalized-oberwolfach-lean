module

public import Oberwolfach.LongSelectedListMargins

@[expose] public section
/-! Choose the original residual error after a fixed positive reserved-list
extension density. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem reserved_spoke_residual_parameter_choice
    (β:ℝ) (hβ:0<β) (hβ1:β≤1):
    ∃θ δ:ℝ,0<θ ∧ θ≤1/100 ∧ 0<δ ∧ 10*θ≤δ ∧ δ≤(β/100)^2:=by
  let δ:ℝ:=(β/100)^2/2
  let θ:ℝ:=min (1/100:ℝ) (δ/20)
  have hδ:0<δ:=by dsimp [δ];positivity
  have hθ:0<θ:=lt_min (by norm_num) (by positivity)
  have hθ1:θ≤1/100:=min_le_left _ _
  have hθδ:θ≤δ/20:=min_le_right _ _
  refine ⟨θ,δ,hθ,hθ1,hδ,?_,?_⟩
  · linarith
  · dsimp [δ];nlinarith [sq_nonneg (β/100)]
end Oberwolfach
