module

public import Oberwolfach.FirstVortexThetaChoice

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_source_cutoff_from_host (m d K:ℕ) (θ:ℝ) (hK:0<K)
    (hcut:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2):
    5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/((K:ℝ)+1)≤θ/2 :=by
  have hKpos:(0:ℝ)<K:=by exact_mod_cast hK
  have hnum:0≤((m:ℝ)+1)*(d:ℝ):=by positivity
  have hfrac:((m:ℝ)+1)*(d:ℝ)/((K:ℝ)+1)≤((m:ℝ)+1)*(d:ℝ)/(K:ℝ):=
    div_le_div_of_nonneg_left hnum hKpos (by linarith)
  linarith
end Oberwolfach
