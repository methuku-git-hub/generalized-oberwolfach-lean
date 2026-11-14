module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! Allocate half the class tolerance to the all-level reference event and
one quarter to each of the two approximate-potential families. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem mixed_class_complete_failure_budget (χ:ℝ) (hχ:0≤χ) (n:ℕ) (hn:0<n):
    100*(χ/2)+107/(n:ℝ)+25*χ+25*χ≤100*χ+200/(n:ℝ):=by
  have hi:0≤(1:ℝ)/(n:ℝ):=by positivity
  have h107:(107:ℝ)/(n:ℝ)=107*(1/(n:ℝ)):=by ring
  have h200:(200:ℝ)/(n:ℝ)=200*(1/(n:ℝ)):=by ring
  linarith
end Oberwolfach
