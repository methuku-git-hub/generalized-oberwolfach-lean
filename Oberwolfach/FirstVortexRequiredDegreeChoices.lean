module

public import Oberwolfach.LongRequiredLocalDegreeMargin

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_required_degree_choices
    (θ ε δ lamMax:ℝ) (hθ:0<θ) (hε:0<ε) (hδ:0<δ) (hmax:0<lamMax):
    ∃lam:ℝ,0<lam ∧ lam≤θ ∧ lam≤lamMax ∧
      ∀(n A:ℕ), ε*n/2≤A→lam*n≤δ*A/16:=by
  let lam:ℝ:=min θ (min lamMax (δ*ε/32))
  have hlam:0<lam:=by dsimp [lam];positivity
  have hlamθ:lam≤θ:=min_le_left _ _
  have hlamMax:lam≤lamMax:=(min_le_right _ _).trans (min_le_left _ _)
  have hlamScale:lam≤δ*ε/32:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨lam,hlam,hlamθ,hlamMax,?_⟩
  intro n A hA
  have hn:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hm:=mul_le_mul_of_nonneg_right hlamScale hn
  have hA':=mul_le_mul_of_nonneg_left hA hδ.le
  nlinarith only [hm,hA']
end Oberwolfach
