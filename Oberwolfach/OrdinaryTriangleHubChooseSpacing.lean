module

public import Oberwolfach.OrdinaryTriangleHubAfterSpacing

@[expose] public section
/-! Choose the triangle terminal-size threshold after the failure allowances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_hub_choose_spacing
    (d:ℕ) (hd:2≤d) (α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap:ℝ)
    (htri:OrdinaryTriangleHubAfterCapBeforeFailure d hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap)
    (εR εH χdeep χHub χone χtwo χcut:ℝ) (hεR:0<εR) (hεH:0<εH) (hχdeep:0<χdeep) (hχHub:0<χHub)
    (hχone:0<χone) (hχtwo:0<χtwo) (hχcut:0<χcut)
    (β:ℝ) (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤α/8) (hβκ:β≤κ) (hβδ:β≤δ) (hgap:ξ+2*β<ηHub):
    ∃v₀:ℕ,1≤v₀ ∧ OrdinaryTriangleHubAfterSpacing d v₀ hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δcap εR εH χdeep χHub χone χtwo χcut β :=by
  exact htri εR εH χdeep χHub χone χtwo χcut hεR hεH hχdeep hχHub hχone hχtwo hχcut β hβ hβ1 hβα hβκ hβδ hgap
end Oberwolfach
