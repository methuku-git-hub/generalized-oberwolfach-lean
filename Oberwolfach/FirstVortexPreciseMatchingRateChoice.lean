module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! Choose the matching rate after θ and a later edit cap so the precise
required-graph degree and first-active matching load budgets both hold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_precise_matching_rate_choice
    (a cap θ upper:ℝ) (ha:0<a) (hcap:0<cap) (hθ:0<θ) (hupper:0<upper):
    ∃lam ξCap:ℝ,0<lam ∧ lam≤upper ∧ lam≤1 ∧ lam≤θ ∧ lam≤cap*a/4096 ∧
      0<ξCap ∧ ∀ξ:ℝ,ξ≤ξCap→lam+ξ≤a*θ/4096 :=by
  let lam:ℝ:=min upper (min 1 (min θ (min (cap*a/4096) (a*θ/8192))))
  let ξCap:ℝ:=a*θ/8192
  have hlam:0<lam:=by dsimp [lam];positivity
  have hlu:lam≤upper:=min_le_left _ _
  have hl1:lam≤1:=(min_le_right _ _).trans (min_le_left _ _)
  have hlθ:lam≤θ:=((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hlcap:lam≤cap*a/4096:=(((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hldeg:lam≤a*θ/8192:=(((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hξCap:0<ξCap:=by dsimp [ξCap];positivity
  refine ⟨lam,ξCap,hlam,hlu,hl1,hlθ,hlcap,hξCap,?_⟩
  intro ξ hξ
  dsimp only [ξCap] at hξ
  linarith only [hξ,hldeg]
end Oberwolfach
