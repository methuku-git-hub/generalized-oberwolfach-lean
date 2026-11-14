module

public import Oberwolfach.OrdinaryWeightedCorrectionAfterTerminal

@[expose] public section
/-! Fix terminal and failure-exponent budgets without changing the already
chosen correction and matching parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_weighted_correction_choose_terminal
    (r d:ℕ) (hd:2 ≤ d) (mAbs a b:ℕ) (α pstar ω εabs εv L ξ:ℝ)
    (hselect:OrdinaryWeightedCorrectionAfterAbsorberChoices r d hd mAbs a b α pstar ω εabs εv L ξ)
    (t f q₀:ℕ):
    ∃N:ℕ,1 ≤ N ∧ OrdinaryWeightedCorrectionAfterTerminal r d hd mAbs a b t f q₀ N α pstar ω εabs εv L ξ :=by
  exact hselect t f q₀
end Oberwolfach
