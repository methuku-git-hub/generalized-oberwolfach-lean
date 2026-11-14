module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! Small parameters for the successor weighting are fixed before b and n.
The later order threshold may depend on b; these choices do not. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem successor_small_parameters (c C η₀ β τ : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hη₀ : 0 < η₀) (hβ : 0 < β) (hτ : 0 < τ) :
    ∃ η ε₀ : ℝ, 0 < η ∧ η < η₀ ∧ 0 < ε₀ ∧ ε₀ ≤ η/2 ∧
      Real.sqrt η ≤ 1/4 ∧ ε₀ + η ≤ β/4 ∧ ε₀ + Real.sqrt η ≤ β/4 ∧
      Real.sqrt η ≤ τ/32 ∧ C*Real.sqrt η ≤ τ/32 ∧ c*(C*Real.sqrt η) ≤ 1/4 := by
  let t := min (1/4 : ℝ) (min η₀ (min (β/64)
    (min (τ/64) (min (τ/(64*C)) (1/(8*c*C))))))
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨s,hs,hst⟩ := exists_between ht
  have hs1 : s < 1/4 := hst.trans_le (min_le_left _ _)
  have hsη : s < η₀ := hst.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsβ : s < β/64 := hst.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hsτ : s < τ/64 := hst.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hsC : s < τ/(64*C) := hst.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))
  have hsc : s < 1/(8*c*C) := hst.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))))
  have hs2 : s^2 ≤ s := by nlinarith
  have hsC' := (lt_div_iff₀ (show (0 : ℝ) < 64*C by positivity)).mp hsC
  have hsc' := (lt_div_iff₀ (show (0 : ℝ) < 8*c*C by positivity)).mp hsc
  refine ⟨s^2,s^2/4,by positivity,lt_of_le_of_lt hs2 hsη,by positivity,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try rw [Real.sqrt_sq hs.le]
  all_goals nlinarith

end Oberwolfach
