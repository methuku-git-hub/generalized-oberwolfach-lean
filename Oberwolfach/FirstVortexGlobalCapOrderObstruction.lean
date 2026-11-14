module

public import Oberwolfach.FirstVortexAllClassesSingleLevelEarlyGlobalPacking

@[expose] public section
/-! The absolute global perturbation cap at the first active level cannot be
combined directly with the current first-vortex packing hierarchy. This
isolates the need for a locally restricted change estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem first_vortex_global_cap_order_obstruction
    (ε θ α ρ₀ C₀ tstar:ℝ) (hε:0<ε) (hθ:0≤θ) (hρ:ρ₀≤1) (hC:1≤C₀)
    (ht:tstar≤1) (hsmall:(2*α)/16≤((ρ₀/4)/40000)*θ/1024)
    (hehi:ε≤α/(1000*C₀)) (hcap:θ≤ε*tstar/512):False :=by
  have hCpos:0<1000*C₀:=by linarith
  have hεmul:ε*(1000*C₀)≤α:=(le_div_iff₀ hCpos).mp hehi
  have hεbase:1000*ε≤α:=by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hC)]
  have hρθ:ρ₀*θ≤θ:=by nlinarith [mul_nonneg hθ (sub_nonneg.mpr hρ)]
  have hαθ:α≤θ:=by nlinarith only [hsmall,hρθ,hθ]
  have hθsmall:θ≤ε/512:=by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr ht)]
  linarith
end Oberwolfach
