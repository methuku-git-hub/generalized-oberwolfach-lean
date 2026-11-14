module

public import Oberwolfach.FirstVortexParentAlignedWeightMonotonicity
public import Oberwolfach.SuccessorPreweightExistence

@[expose] public section
/-! Instantiate the parent-tolerance comparison at the distinct weight bound
actually selected for the parent and active levels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_actual_parent_selected_weights
    (r k₀:ℕ) (αRef ρ₀ tstar BA δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff:ℝ)
    (hα:0<αRef) (hρ:0<ρ₀) (hε:0<ε)
    (hBA:successorWeightUpper k₀ ((2*αRef)/4)≤BA)
    (h:FirstVortexActualParentAlignedRates r ρ₀ (1/100) tstar BA δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff):
    FirstVortexActualParentAlignedRates r ρ₀ (1/100) tstar (successorWeightUpper k₀ ((2*αRef)/4))
      δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff :=by
  have hB:0≤successorWeightUpper k₀ ((2*αRef)/4):=
    (successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2.le
  exact first_vortex_parent_aligned_weight_monotonicity r ρ₀ (1/100) tstar _ BA δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff
    hρ (by norm_num) hε hB hBA h
end Oberwolfach
