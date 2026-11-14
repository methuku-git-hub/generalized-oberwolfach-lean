module

public import Oberwolfach.LongCapacityAutomaticMargins

@[expose] public section
/-! The ordinary-class path capacity needs the same cutoff choice and an
order threshold depending on its smaller positive activity threshold. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace Oberwolfach

theorem ordinary_capacity_automatic_margins (m d K:ℕ) (hK:0<K) (θ:ℝ) (hθ:0<θ)
    (hcut:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2):
    (5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2) ∧
    ∃N:ℕ,∀n≥N,4*((m:ℝ)+1)/(θ*(θ/100))<(n:ℝ)^((1:ℝ)/4):=by
  refine ⟨long_capacity_cutoff_succ m d K hK θ hcut,?_⟩
  have ht:Filter.Tendsto (fun n:ℕ=>(n:ℝ)^((1:ℝ)/4)) Filter.atTop Filter.atTop:=
    (tendsto_rpow_atTop (y:=(1:ℝ)/4) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hh:=ht.eventually (eventually_gt_atTop (4*((m:ℝ)+1)/(θ*(θ/100))))
  exact Filter.eventually_atTop.1 hh
end Oberwolfach
