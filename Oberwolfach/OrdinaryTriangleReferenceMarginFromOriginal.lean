module

public import Oberwolfach.Definitions
public import Mathlib.Tactic

@[expose] public section
/-! Retain a positive triangle-reference margin inside the original host
minimum-degree surplus, before any finite host is chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_reference_margin_from_original
    (θ α₀:ℝ) (hθhalf:1/2≤θ) (hθcycle:cycleThreshold 3≤θ) (hθ1:θ<1) (hα₀:0<α₀):
    ∃α:ℝ,0<α ∧ α≤1/2 ∧ max (1/2) (cycleThreshold 3)+α/2≤1 ∧
      max (1/2) (cycleThreshold 3)+2*α≤θ+α₀ :=by
  let α:=min (α₀/4) (min ((1-θ)/4) (1/4:ℝ))
  have ht:0<1-θ:=by linarith
  have hα:0<α:=by dsimp [α];positivity
  have hα₀':α≤α₀/4:=min_le_left _ _
  have hαθ:α≤(1-θ)/4:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hα1:α≤1/4:=le_trans (min_le_right _ _) (min_le_right _ _)
  have hθ:max (1/2) (cycleThreshold 3)≤θ:=max_le hθhalf hθcycle
  exact ⟨α,hα,by linarith,by linarith,by linarith⟩
end Oberwolfach
