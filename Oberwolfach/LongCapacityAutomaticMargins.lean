module

public import Oberwolfach.LongCompatibleParameterChoices
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
/-! The fixed cutoff inequality persists at K+1, and the remaining order
condition holds for all sufficiently large n. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace Oberwolfach

theorem long_capacity_cutoff_succ (m d K:ℕ) (hK:0<K) (θ:ℝ)
    (h:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2):
    5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2:=by
  have hKpos:(0:ℝ)<K:=by exact_mod_cast hK
  have hquot:((m:ℝ)+1)*(d:ℝ)/((K:ℝ)+1)≤((m:ℝ)+1)*(d:ℝ)/(K:ℝ):=by
    apply div_le_div_of_nonneg_left (by positivity) hKpos
    linarith
  linarith

theorem long_capacity_large_order (m:ℕ) (θ:ℝ) (hθ:0<θ):
    ∃N:ℕ,∀n≥N,8*((m:ℝ)+1)/θ<(n:ℝ)^((1:ℝ)/4):=by
  have ht:Filter.Tendsto (fun n:ℕ=>(n:ℝ)^((1:ℝ)/4)) Filter.atTop Filter.atTop:=
    (tendsto_rpow_atTop (y:=(1:ℝ)/4) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hh:=ht.eventually (eventually_gt_atTop (8*((m:ℝ)+1)/θ))
  exact Filter.eventually_atTop.1 hh
end Oberwolfach
