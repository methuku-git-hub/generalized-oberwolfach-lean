module

public import Oberwolfach.ReservedSpokeResidualParameters

@[expose] public section
/-! Choose θ below any previously fixed positive threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem reserved_spoke_residual_parameter_choice_below
    (β η:ℝ) (hβ:0<β) (hβ1:β≤1) (hη:0<η):
    ∃θ δ:ℝ,0<θ ∧ θ≤η ∧ θ≤1/100 ∧ 0<δ ∧ 10*θ≤δ ∧ δ≤(β/100)^2:=by
  obtain ⟨θ₀,δ,hθ₀,hθmax,hδ,hθδ,hδbound⟩:=reserved_spoke_residual_parameter_choice β hβ hβ1
  let θ:=min θ₀ η
  have hθ:0<θ:=lt_min hθ₀ hη
  have hle:θ≤θ₀:=min_le_left _ _
  refine ⟨θ,δ,hθ,min_le_right _ _,hle.trans hθmax,hδ,?_,hδbound⟩
  linarith
end Oberwolfach
