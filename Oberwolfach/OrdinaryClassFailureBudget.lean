module

public import Oberwolfach.OrdinaryCombinedFullHostInputs

@[expose] public section
/-! The explicit ordinary common-event error is below the class probability
budget used by the simultaneous protected partition. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_combined_failure_below_class_budget (n:ℕ) (hn:1≤n) (χ:ℝ) (hχ:0≤χ):
    1/(n:ℝ)+3/(n:ℝ)^2≤100*χ+200/(n:ℝ):=by
  have hn1:(1:ℝ)≤n:=by exact_mod_cast hn
  have hn0:(0:ℝ)<n:=by linarith
  have hi:(1:ℝ)/(n:ℝ)^2≤1/(n:ℝ):=by
    apply (div_le_div_iff₀ (by positivity) hn0).2
    nlinarith
  have hp:(0:ℝ)≤1/(n:ℝ):=by positivity
  have h3:(3:ℝ)/(n:ℝ)^2=3*(1/(n:ℝ)^2):=by ring
  have h200:(200:ℝ)/(n:ℝ)=200*(1/(n:ℝ)):=by ring
  rw [h3,h200]
  nlinarith
end Oberwolfach
