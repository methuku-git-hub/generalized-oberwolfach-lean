module

public import Oberwolfach.FiberwiseCandidateAssignment
public import Oberwolfach.MatchingFrequencyMargin

@[expose] public section
/-! The upper frequency error leaves enough original components for the
selected candidates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem approximate_selected_count_le_capacity
    (a t:ℕ) (θ lam:ℝ) (hlamθ:lam≤θ)
    (herr:|((a:ℝ)-(1-θ)*t)|≤lam*t):a≤t :=by
  have hmul:lam*(t:ℝ)≤θ*t:=mul_le_mul_of_nonneg_right hlamθ (by positivity)
  have hu:=le_abs_self ((a:ℝ)-(1-θ)*t)
  have ha:(a:ℝ)≤t:=by nlinarith
  exact_mod_cast ha

theorem approximate_fiberwise_component_assignment
    {C D K:Type} [DecidableEq C] [DecidableEq D] [DecidableEq K]
    (A:Finset C) (B:Finset D) (f:C→K) (g:D→K) (θ lam:ℝ) (hlamθ:lam≤θ)
    (herr:∀k,|(((A.filter (fun c=>f c=k)).card:ℝ)-(1-θ)*(B.filter (fun d=>g d=k)).card)|≤
      lam*(B.filter (fun d=>g d=k)).card):
    ∃h:{c // c∈A}↪{d // d∈B},∀c,g (h c).val=f c.val :=by
  apply fiberwise_injective_assignment A B f g
  intro k
  exact approximate_selected_count_le_capacity _ _ θ lam hlamθ (herr k)
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem approximate_selected_real_target_le_capacity
    (a cap:ℕ) (t θ lam:ℝ) (ht:0≤t) (hcap:t≤cap) (hlamθ:lam≤θ)
    (herr:|((a:ℝ)-(1-θ)*t)|≤lam*t):a≤cap :=by
  have hmul:lam*t≤θ*t:=mul_le_mul_of_nonneg_right hlamθ ht
  have hu:=le_abs_self ((a:ℝ)-(1-θ)*t)
  have ha:(a:ℝ)≤cap:=by nlinarith
  exact_mod_cast ha
end Oberwolfach
