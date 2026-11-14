module

public import Oberwolfach.MarkedSpokeToleranceMonotone

@[expose] public section
/-! The retained-load error may be chosen after the fixed domain ratio K. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_larger_hub_load_error_choice (η cap C K:ℝ)
    (hη:0<η) (hcap:0<cap) (hC:0≤C) (hK:0≤K):
    ∃ ζ:ℝ,0<ζ ∧ ζ≤cap ∧ C*K*ζ≤η/16:=by
  let ζ:=min cap (η/(16*(1+C*K)))
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have hζcap:ζ≤cap:=min_le_left _ _
  have hζbound:ζ≤η/(16*(1+C*K)):=min_le_right _ _
  have hck:0≤C*K:=mul_nonneg hC hK
  have hp:(0:ℝ)<16*(1+C*K):=by positivity
  have hb:ζ*(16*(1+C*K))≤η:=(le_div_iff₀ hp).mp hζbound
  refine ⟨ζ,hζ,hζcap,?_⟩
  nlinarith
end Oberwolfach
