module

public import Oberwolfach.LongReferenceParentLoadScaleAlignment

@[expose] public section
/-! Translate the selected uniform-level load and geometry budgets into the
exact reference-scale inequalities required by the selected-outcome theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem long_selected_selector_load_margins
    (r:ℕ) (ρ₀ ρ s₀ tstar B δ ε κ thetaDeep η xiDeep omegaInner hIcut:ℝ)
    (ht:tstar=s₀/(((r+4):ℕ):ℝ)) (hρ:ρ₀≤ρ)
    (hGap:∀rho t:ℝ,ρ₀≤rho→tstar≤t→(1+2/rho)*xiDeep≤t*omegaInner/32)
    (hParent:δ+δ+11*(((r+4:ℕ):ℝ)+1)^4*(2*B/(ρ₀*tstar/2)^(2*(r+4)+1))*δ≤κ/4)
    (hDeep:δ+δ+11*(((r+4:ℕ):ℝ)+1)^4*(2*B/(ρ₀*tstar/2)^(2*(r+4)+1))*δ≤thetaDeep/4)
    (hLocal:δ+δ+5*(((r+4:ℕ):ℝ)+1)^4*(2*B/(ρ₀*tstar/2)^(2*(r+4)+1))*(4/ε)*δ≤η/4)
    (hRow:δ+δ≤tstar/8) (hCut:2*hIcut≤tstar/8-δ):
    (1+2/ρ)*xiDeep≤(s₀/(((r+4):ℕ):ℝ))*omegaInner/32 ∧
    δ+δ+11*(((r+4:ℕ):ℝ)+1)^4*(2*B/(ρ₀*s₀/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*δ≤κ/4 ∧
    δ+δ+11*(((r+4:ℕ):ℝ)+1)^4*(2*B/(ρ₀*s₀/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*δ≤thetaDeep/4 ∧
    δ+δ+5*(((r+4:ℕ):ℝ)+1)^4*(2*B/(ρ₀*s₀/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*δ≤η/4 ∧
    δ+δ≤(s₀/(((r+4):ℕ):ℝ))/8 ∧ 2*hIcut≤tstar/8-δ := by
  have hscale:=long_reference_parent_load_scale_alignment (r+4) ρ₀ s₀ tstar ht
  refine ⟨hGap ρ (s₀/(((r+4):ℕ):ℝ)) hρ (le_of_eq ht),?_,?_,?_,?_,hCut⟩
  · simpa only [←hscale] using hParent
  · simpa only [←hscale] using hDeep
  · simpa only [←hscale] using hLocal
  · simpa only [ht] using hRow
end Oberwolfach
