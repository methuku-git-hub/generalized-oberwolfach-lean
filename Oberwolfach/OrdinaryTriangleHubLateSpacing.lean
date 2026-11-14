module

public import Oberwolfach.OrdinaryTriangleHubChooseSpacing

@[expose] public section
/-! Choose the vortex error and terminal threshold after the triangle
selector reveals its cap, while keeping the earlier edit tolerance fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_hub_late_spacing
    (d:ℕ) (hd:2≤d) (α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap capξ:ℝ)
    (hδ:0<δ)
    (hβchoose:∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤κ ∧ β≤capξ ∧ β≤betaCap ∧ ξ+2*β<ηHub)
    (htri:OrdinaryTriangleHubAfterCapBeforeFailure d hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap)
    (εR εH χdeep χHub χone χtwo χcut:ℝ) (hεR:0<εR) (hεH:0<εH) (hχdeep:0<χdeep) (hχHub:0<χHub)
    (hχone:0<χone) (hχtwo:0<χtwo) (hχcut:0<χcut)
    (betaCap:ℝ) (hBetaCap:0<betaCap):
    ∃β:ℝ,0<β ∧ β≤betaCap ∧ ∃v₀:ℕ,1≤v₀ ∧
      OrdinaryTriangleHubAfterSpacing d v₀ hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δcap εR εH χdeep χHub χone χtwo χcut β :=by
  obtain ⟨β,hβ,hβ1,hβα,hβκ,hβcap,hβlate,hgap⟩:=hβchoose (min δ betaCap) (by positivity)
  have hβδ:β≤δ:=hβlate.trans (min_le_left _ _)
  have hβuser:β≤betaCap:=hβlate.trans (min_le_right _ _)
  obtain ⟨v₀,hv₀,hafter⟩:=ordinary_triangle_hub_choose_spacing d hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap htri
    εR εH χdeep χHub χone χtwo χcut hεR hεH hχdeep hχHub hχone hχtwo hχcut β hβ.le hβ1 hβα hβκ hβδ hgap
  exact ⟨β,hβ,hβuser,v₀,hv₀,hafter⟩
end Oberwolfach
