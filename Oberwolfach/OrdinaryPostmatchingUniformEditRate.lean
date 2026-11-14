module

public import Oberwolfach.OrdinaryActualPhysicalRateBudget

@[expose] public section

/-! Choose the original edit rate before the sample and all target edits,
while allowing the placement and matching rates to be chosen earlier. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_postmatching_uniform_edit_rate
    (bList bRate bMatch : ℝ) (d : ℕ)
    (hList : 0 < bList) (hRate : 0 < bRate) (hMatch : 0 < bMatch) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ bList / 8 ∧ ξ ≤ bRate / 16 ∧ ξ ≤ bMatch ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ((6*d+4:ℕ):ℝ) ≤ (bRate / 16) * n ∧
        2 * (2 * ((3*d:ℕ):ℝ)) ≤ (bRate / 16) * n := by
  let ξ : ℝ := min (bList / 8) (min (bRate / 16) bMatch) / 2
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hl : ξ ≤ bList / 8 := by
    have hmin := min_le_left (bList / 8) (min (bRate / 16) bMatch)
    dsimp [ξ]; linarith
  have hr : ξ ≤ bRate / 16 := by
    have hmin := le_trans (min_le_right (bList / 8) (min (bRate / 16) bMatch))
      (min_le_left (bRate / 16) bMatch)
    dsimp [ξ]; linarith
  have hm : ξ ≤ bMatch := by
    have hmin := le_trans (min_le_right (bList / 8) (min (bRate / 16) bMatch))
      (min_le_right (bRate / 16) bMatch)
    dsimp [ξ]; linarith
  obtain ⟨N₁,hN₁⟩ := ordinary_constant_eventually_below_linear_rate (bRate/16)
    ((6*d+4:ℕ):ℝ) (by positivity)
  obtain ⟨N₂,hN₂⟩ := ordinary_constant_eventually_below_linear_rate (bRate/16)
    (2 * (2 * ((3*d:ℕ):ℝ))) (by positivity)
  refine ⟨ξ,hξ,hl,hr,hm,max N₁ N₂,?_⟩
  intro n hn
  exact ⟨hN₁ n (le_trans (le_max_left _ _) hn),
    hN₂ n (le_trans (le_max_right _ _) hn)⟩
end Oberwolfach
