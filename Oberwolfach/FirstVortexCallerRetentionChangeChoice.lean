module

public import Oberwolfach.FirstVortexOrderedSummedLossRetentionParameters

@[expose] public section
/-! Reuse the caller's retention choice and the global transfer budget in the
same later chain continuation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_caller_retention_change_choice
    (r d:ℕ) (ε active θ s c ζret ζlocal ηBalance κaux cap capStable cLocal:ℝ)
    (hret:FirstVortexRetentionBalanceRates r d ε active θ s c ζret ζlocal ηBalance κaux)
    (hactive:0<active) (hcap:0<cap) (hcapStable:cap≤capStable)
    (hactiveGlobal:active≤(min cap (1:ℝ))/2) (hactiveLocal:active≤cLocal):
    ∃ζRet ζChange:ℝ,
      0≤ζRet ∧ ζRet≤active/128 ∧ ζret≤ζRet*ε/2 ∧
      0≤ζChange ∧ ζChange≤capStable ∧ active≤ζChange ∧
      (min cap (1:ℝ))/2≤ζChange ∧ 0≤cLocal ∧ active≤cLocal :=by
  rcases hret with ⟨_,hζlocal,_,_,_,_,_,hζlocalCap,hζretLocal,_⟩
  have hmin:0<min cap (1:ℝ):=lt_min hcap (by norm_num)
  have hminCap:min cap (1:ℝ)≤cap:=min_le_left _ _
  refine ⟨ζlocal,(min cap (1:ℝ))/2,hζlocal.le,hζlocalCap,hζretLocal,by positivity,?_,hactiveGlobal,le_rfl,by linarith,hactiveLocal⟩
  linarith
end Oberwolfach
