module

public import Oberwolfach.OrdinaryTriangleSeparatedNumericScales

@[expose] public section
/-! The host regularity tolerance can be chosen after the separated
geometric scale and before the host, with the exact parent balance bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_parent_balance_scale_choice
    (ρ₀ p η b cap:ℝ) (hρ₀:0<ρ₀) (hp:0<p) (hη:0<η) (hcap:0<cap)
    (hb:2*b≤(ρ₀/16)*p*η):
    ∃β₀:ℝ,0<β₀ ∧ β₀≤cap ∧
      ∀β:ℝ,β≤β₀→β+2*b≤2*(ρ₀/16)*p*η :=by
  let β₀:=min cap ((ρ₀/16)*p*η)
  have hβ:0<β₀:=lt_min hcap (by positivity)
  have hβcap:β₀≤cap:=min_le_left _ _
  have hβbal:β₀≤(ρ₀/16)*p*η:=min_le_right _ _
  refine ⟨β₀,hβ,hβcap,?_⟩
  intro β hβsmall
  linarith
end Oberwolfach
