module

public import Oberwolfach.LongActualUniformReferenceLevelStep

@[expose] public section
/-! The level theorem selected with geometric parameter alphaHost/2 has
exactly the inner density used by the actual-host selector. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach

theorem long_host_selected_actual_level_step
    (r d N NI Kgeom:ℕ)
    (αHost ρ₀ ρ tstar kstar betaA A B κ ξ thetaDeep omegaInner ε betaRec η x hIcut deltaI etaBal gammaLoss sigmaLoss extra:ℝ)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1) (ht:0<tstar)
    (htcap:tstar≤(1/100)/(((r+4):ℕ):ℝ)) (hk:0<kstar)
    (hkcap:kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
    (hSteps:∀rho omega t:ℝ,ρ₀≤rho → rho≤1 → ρ₀/8≤omega → omega≤1 → tstar≤t → (r+4:ℝ)*t≤1 →
      ρ₀/400≤rho*(r+4:ℝ)*t/2 → kstar≤rho*(r+4:ℝ)*t/2 → kstar≤rho*t/2 → kstar≤t →
      ∀(Gamma Color:Type) [Fintype Gamma] [Fintype Color],
      ∀ level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom (αHost/16) rho omega t kstar betaA A B
        κ ξ thetaDeep ((αHost/2)/4) omegaInner (ε/4) betaRec A B η x (ρ₀/16) hIcut deltaI etaBal,
        MarkedReferenceLevelStepProperty level (gammaLoss+extra) (sigmaLoss+extra)):
    ∀ level:MarkedReferenceLevelData Bool Bool r d N NI Kgeom (αHost/16) ρ (ρ₀/8)
      ((1/100)/(((r+4):ℕ):ℝ)) kstar betaA A B κ ξ thetaDeep (αHost/8) omegaInner (ε/4)
      betaRec A B η x (ρ₀/16) hIcut deltaI etaBal,
      MarkedReferenceLevelStepProperty level (gammaLoss+extra) (sigmaLoss+extra) := by
  have hscale:(αHost/2)/4=αHost/8 := by ring
  apply long_actual_uniform_reference_level_step r d N NI Kgeom αHost ρ₀ ρ tstar kstar
    betaA A B κ ξ thetaDeep omegaInner ε betaRec η x hIcut deltaI etaBal gammaLoss sigmaLoss extra
    hρ₀ hρlo hρhi ht htcap hk hkcap
  rw [hscale] at hSteps
  exact hSteps
end Oberwolfach
