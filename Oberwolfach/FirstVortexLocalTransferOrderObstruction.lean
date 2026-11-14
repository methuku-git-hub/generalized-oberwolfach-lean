module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! A small absolute first-active change cap cannot be combined with the
packing hierarchy when the proposed error bound still contains θ at full
first-vortex scale. This concerns that transfer route, not the theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_local_transfer_order_obstruction
    (α a cap θ:ℝ) (hα:0<α) (ha:0≤a) (ha1:a≤1)
    (hθ:0≤θ) (hcap:cap≤α) (hsmall:θ≤cap/128)
    (hpacking:(2*α)/16≤a*θ/1024):False :=by
  have haθ:a*θ≤θ:=by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hθ]
  nlinarith only [hα,hcap,hsmall,hpacking,haθ]
end Oberwolfach
