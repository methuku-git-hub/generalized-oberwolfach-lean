module

public import Oberwolfach.OrdinaryFirstVortexCorrectionThresholdShape

@[expose] public section
/-! Select the size threshold before the sample and factor family. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_first_vortex_correction_choose_threshold
    (θhost α ρ₀ βfreq ε εabs εv:ℝ) (hθ:(1/2:ℝ) ≤ θhost) (hα:0<α)
    (hρ₀:0<ρ₀) (hρ₀1:ρ₀ ≤ 1) (hβ:0<βfreq) (hβ1:βfreq ≤ 1)
    (hε:0<ε) (habs:ε ≤ εabs) (hv:ε ≤ εv) (Nc Ng Nh Ncol:ℕ):
    ∃N:ℕ,1 ≤ N ∧ OrdinaryFirstVortexCorrectionThresholdShape N Nc Ng Nh Ncol θhost α ρ₀ βfreq ε εabs εv :=by
  exact ordinary_original_first_vortex_correction_inputs θhost α ρ₀ βfreq ε εabs εv hθ hα hρ₀ hρ₀1 hβ hβ1 hε habs hv Nc Ng Nh Ncol
end Oberwolfach
