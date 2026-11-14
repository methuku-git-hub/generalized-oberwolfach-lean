module

public import Oberwolfach.MarkedReferenceLevelData

@[expose] public section
/-! Raising the global threshold only strengthens the two lower-size fields
of a reference-level record. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N₁ N₂ NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}
def marked_reference_level_lower_threshold
    (L:MarkedReferenceLevelData Gamma Color r d N₂ NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (hN:N₁≤N₂):
    MarkedReferenceLevelData Gamma Color r d N₁ NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal:=
  { L with hnP:=hN.trans L.hnP, hnW:=hN.trans L.hnW }
end Oberwolfach
namespace Oberwolfach
/-- A bounded absorber fits into each positive linear reserve once the order
is sufficiently large. The threshold is chosen after the reserve densities. -/
theorem bounded_card_fits_two_linear_reserves
    (e₀:ℕ) (δ₁ δ₂:ℝ) (hδ₁:0<δ₁) (hδ₂:0<δ₂):
    ∃ N:ℕ,1≤N∧∀ n:ℕ,N≤n→(e₀:ℝ)≤min δ₁ δ₂*n:=by
  have hδ:0<min δ₁ δ₂:=lt_min hδ₁ hδ₂
  obtain ⟨N,hN⟩:=exists_nat_gt (max 1 ((e₀:ℝ)/(min δ₁ δ₂)))
  refine ⟨N,?_,?_⟩
  · have h1:(1:ℝ)<N:=(le_max_left _ _).trans_lt hN
    exact_mod_cast (show (1:ℝ)≤N from le_of_lt h1)
  · intro n hn
    have hnR:(N:ℝ)≤n:=by exact_mod_cast hn
    have hh:(e₀:ℝ)/(min δ₁ δ₂)≤n:=
      ((le_max_right _ _).trans (le_of_lt hN)).trans hnR
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hh
end Oberwolfach
