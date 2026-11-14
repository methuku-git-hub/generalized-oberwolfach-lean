module

public import Mathlib.Tactic

@[expose] public section
/-! Choose a host margin before the failure probability, while leaving the
original edit allowance available to the eventual protected vortex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_original_margin_and_edit_budget
    (α₀ εmax:ℝ) (hα₀:0<α₀) (hεmax:0<εmax):
    ∃α:ℝ,0<α ∧ α≤α₀ ∧
      (∀αRef:ℝ,2*αRef≤α/2→(2*αRef)/100000≤εmax) ∧
      (∀θ D:ℝ,∀n:ℕ,(θ+α₀)*(n:ℝ)≤D→(θ+α)*(n:ℝ)≤D) :=by
  let α:ℝ:=min α₀ (50000*εmax)
  have hα:0<α:=by dsimp [α];positivity
  have hα₀cap:α≤α₀:=min_le_left _ _
  have hεcap:α≤50000*εmax:=min_le_right _ _
  refine ⟨α,hα,hα₀cap,?_,?_⟩
  · intro αRef href
    linarith
  · intro θ D n hD
    have hn:0≤(n:ℝ):=by positivity
    nlinarith only [hD,mul_nonneg (sub_nonneg.mpr hα₀cap) hn]
end Oberwolfach
