module

public import Oberwolfach.OrdinaryReservedEarlyParameters

@[expose] public section

/-! The cutoff-independent reserve floor supplies both physical and hub
density lower bounds required by the common event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_assigned_reserve_density_lower
    (ρ₀ ρ smin rsv pstar:ℝ)
    (hρ₀:0≤ρ₀) (hρ₀1:ρ₀≤1) (hρ:ρ₀≤ρ)
    (hs:0≤smin) (hsr:smin≤rsv) (hp:2*pstar≤ρ₀*smin):
    pstar≤ρ*rsv/2 ∧ pstar≤rsv :=by
  have hR:0≤rsv:=hs.trans hsr
  have hρmul:ρ₀*smin≤ρ*rsv:=by
    nlinarith [mul_nonneg hρ₀ (sub_nonneg.mpr hsr),mul_nonneg hR (sub_nonneg.mpr hρ)]
  have hsbound:ρ₀*smin≤rsv:=by
    nlinarith [mul_nonneg hs (sub_nonneg.mpr hρ₀1)]
  have hp0:0≤ρ₀*smin:=mul_nonneg hρ₀ hs
  constructor <;> nlinarith
end Oberwolfach
