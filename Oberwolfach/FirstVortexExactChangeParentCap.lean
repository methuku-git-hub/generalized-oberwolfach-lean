module

public import Oberwolfach.FirstVortexExactParentCapBound
public import Oberwolfach.FirstVortexExactChangeCap

@[expose] public section
/-! The exact retained change tolerance satisfies the same parent correction
cap selected before the later geometric parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option maxRecDepth 32768
noncomputable section
namespace Oberwolfach

theorem first_vortex_exact_change_parent_cap
    (r:ℕ) (α ρ₀ κ ζCfg thetaDeep BA cap ζChange:ℝ) (hα:0<α) (hρ₀:0<ρ₀)
    (hcap:0≤cap)
    (hChosen:FirstVortexExactParentCapBound r α ρ₀ κ ζCfg thetaDeep BA cap hα hρ₀)
    (hExact:ζChange=(min cap (1:ℝ))/2):
    FirstVortexExactParentCapBound r α ρ₀ κ ζCfg thetaDeep BA ζChange hα hρ₀ :=by
  obtain ⟨hκ,hζ,hθ,hB,hBound⟩:=hChosen
  refine ⟨hκ,hζ,hθ,hB,?_⟩
  apply le_trans ?_ hBound
  rw [hExact]
  have hmin:min cap (1:ℝ)≤cap:=min_le_left _ _
  linarith only [hcap,hmin]
end Oberwolfach
