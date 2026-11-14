module

public import Oberwolfach.LongActualReferenceLevelDensities
public import Oberwolfach.MarkedReferenceLevelStepProperty

@[expose] public section
/-! Specialize the uniform level-step theorem to the actual host density and
reference scale used in the selected vortex chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_actual_uniform_reference_level_step
    (r d N NI Kgeom:ℕ)
    (αHost ρ₀ ρ tstar kstar betaA A B κ ξ thetaDeep omegaInner ε betaRec η x hIcut deltaI etaBal gammaLoss sigmaLoss extra:ℝ)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1) (ht:0<tstar)
    (htcap:tstar≤(1/100)/(((r+4):ℕ):ℝ)) (hk:0<kstar)
    (hkcap:kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
    (hSteps:∀rho omega t:ℝ,ρ₀≤rho → rho≤1 → ρ₀/8≤omega → omega≤1 → tstar≤t → (r+4:ℝ)*t≤1 →
      ρ₀/400≤rho*(r+4:ℝ)*t/2 → kstar≤rho*(r+4:ℝ)*t/2 → kstar≤rho*t/2 → kstar≤t →
      ∀(Gamma Color:Type) [Fintype Gamma] [Fintype Color],
      ∀ level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom (αHost/16) rho omega t kstar betaA A B
        κ ξ thetaDeep (αHost/8) omegaInner (ε/4) betaRec A B η x (ρ₀/16) hIcut deltaI etaBal,
        MarkedReferenceLevelStepProperty level (gammaLoss+extra) (sigmaLoss+extra)):
    ∀ level:MarkedReferenceLevelData Bool Bool r d N NI Kgeom (αHost/16) ρ (ρ₀/8)
      ((1/100)/(((r+4):ℕ):ℝ)) kstar betaA A B κ ξ thetaDeep (αHost/8) omegaInner (ε/4)
      betaRec A B η x (ρ₀/16) hIcut deltaI etaBal,
      MarkedReferenceLevelStepProperty level (gammaLoss+extra) (sigmaLoss+extra) := by
  obtain ⟨hρ₀1,hω,hω1,ht0,ht1,hp0,hp01,hk0,hk1,htle,hmt,hpBound,hkBound,hkHalf,hkt⟩:=
    long_actual_reference_level_densities (r+4) (by omega) ρ₀ ρ tstar kstar hρ₀ hρlo hρhi ht htcap hk hkcap
  intro level
  apply hSteps ρ (ρ₀/8) ((1/100)/(((r+4):ℕ):ℝ)) hρlo hρhi le_rfl hω1 htle
  · simpa only [Nat.cast_add,Nat.cast_ofNat] using hmt
  · simpa only [Nat.cast_add,Nat.cast_ofNat] using hpBound
  · simpa only [Nat.cast_add,Nat.cast_ofNat] using hkBound
  · exact hkHalf
  · exact hkt
end Oberwolfach
