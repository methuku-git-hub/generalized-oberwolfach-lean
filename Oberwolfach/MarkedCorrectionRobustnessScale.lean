module

public import Mathlib.Tactic

@[expose] public section
/-! Choose the sparse marked correction below both the routing margin and
the robustness budget of the selected absorber. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_correction_robustness_scale (q:ℕ) (h ζ:ℝ) (hh:0<h) (hζ:0<ζ):
    ∃ξ:ℝ,0<ξ ∧ ((q:ℝ)+1)*ξ≤h/100 ∧
      16*((q:ℝ)+1)*ξ≤ζ ∧ 8*((q:ℝ)+1)*ξ≤ζ:=by
  let c:ℝ:=(q:ℝ)+1
  have hc:0<c:=by dsimp [c];positivity
  let ξ:=min (h/(200*c)) (ζ/(32*c))
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hξh:ξ≤h/(200*c):=min_le_left _ _
  have hξζ:ξ≤ζ/(32*c):=min_le_right _ _
  have hh':ξ*(200*c)≤h:=(le_div_iff₀ (by positivity)).mp hξh
  have hζ':ξ*(32*c)≤ζ:=(le_div_iff₀ (by positivity)).mp hξζ
  refine ⟨ξ,hξ,?_,?_,?_⟩ <;> dsimp [c] at * <;> nlinarith [mul_nonneg hc.le hξ.le]
end Oberwolfach
