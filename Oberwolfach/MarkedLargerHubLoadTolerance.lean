module

public import Oberwolfach.MarkedLargerHubLoadErrorChoice

@[expose] public section
/-! Choose the retained-load error after the domain ratio so that it fits
the active level's error allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_larger_hub_load_tolerance (η cap C K τ tol:ℝ)
    (hη:0<η) (hcap:0<cap) (hC:0≤C) (hK:0≤K) (hbase:τ+tol≤η/8):
    ∃ ζ:ℝ,0<ζ ∧ ζ≤cap ∧ τ+tol+C*K*ζ≤η/4:=by
  obtain ⟨ζ,hζ,hcap',hbound⟩:=marked_larger_hub_load_error_choice η cap C K hη hcap hC hK
  refine ⟨ζ,hζ,hcap',?_⟩
  linarith
end Oberwolfach
