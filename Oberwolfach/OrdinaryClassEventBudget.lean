module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! The ordinary class failure probability fits the common event budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_class_event_budget (n:ℕ) (hn:0<n) (χ:ℝ) (hχ:0≤χ):
    1/(n:ℝ)+2/(n:ℝ)^2≤100*χ+200/(n:ℝ):=by
  have hnR:(1:ℝ)≤n:=by exact_mod_cast hn
  have hp:(0:ℝ)<n:=by positivity
  have hInv:(1:ℝ)/(n:ℝ)≤1:=by rw [div_le_one hp];exact hnR
  have hInv0:0≤(1:ℝ)/(n:ℝ):=by positivity
  have heq:(1:ℝ)/(n:ℝ)^2=(1/(n:ℝ))^2:=by ring
  have h2:(2:ℝ)/(n:ℝ)^2=2*((1:ℝ)/(n:ℝ)^2):=by ring
  have h200:(200:ℝ)/(n:ℝ)=200*((1:ℝ)/(n:ℝ)):=by ring
  nlinarith
end Oberwolfach
