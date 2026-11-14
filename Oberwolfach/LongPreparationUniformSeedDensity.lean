module

public import Oberwolfach.LongPreparationFamilySeeds

@[expose] public section
/-! A seed-density lower bound can be fixed using the uniform density lower
bound before the graph, factor family, and selected short lengths are known. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_preparation_uniform_seed_density (m:ℕ) (ρ₀ ρ:ℝ)
    (hρ₀:0<ρ₀) (hρ:ρ₀≤ρ):
    let c:ℝ:=(m:ℝ)+1
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*c)));
    0<pstar ∧ pstar≤1/4 ∧ pstar≤ρ/8 ∧ pstar≤ρ/(6*c):=by
  intro c pstar
  have hc:0<c:=by dsimp [c];positivity
  have hp:0<pstar:=by dsimp [pstar];positivity
  have h₁:pstar≤1/4:=min_le_left _ _
  have h₂:pstar≤ρ₀/8:=le_trans (min_le_right _ _) (min_le_left _ _)
  have h₃:pstar≤ρ₀/(6*c):=le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨hp,h₁,h₂.trans ?_,h₃.trans ?_⟩
  · exact div_le_div_of_nonneg_right hρ (by norm_num)
  · exact div_le_div_of_nonneg_right hρ (by positivity)
end Oberwolfach
