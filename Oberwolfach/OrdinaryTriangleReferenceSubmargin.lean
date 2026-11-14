module

public import Oberwolfach.OrdinaryGeneralReferenceMarginFromOriginal

@[expose] public section
/-! A positive triangle reference margin is chosen inside the original host
margin before any sample or finite-size threshold is selected. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_reference_submargin
    (θ α₀:ℝ) (hθhalf:1/2≤θ) (hθcycle:cycleThreshold 3≤θ) (hθ1:θ<1) (hα₀:0<α₀):
    ∃α:ℝ,0<α ∧ α≤α₀ ∧ α≤1 ∧ max (1/2) (cycleThreshold 3)+α/4≤1 :=by
  let α:ℝ:=min (α₀/2) (min ((1-θ)/2) (1/2:ℝ))
  have hα:0<α:=by dsimp [α];positivity
  have hα₀':α≤α₀/2:=min_le_left _ _
  have hαθ:α≤(1-θ)/2:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hαone:α≤1/2:=le_trans (min_le_right _ _) (min_le_right _ _)
  have hθ:max (1/2) (cycleThreshold 3)≤θ:=max_le hθhalf hθcycle
  exact ⟨α,hα,by linarith,by linarith,by linarith⟩
end Oberwolfach
