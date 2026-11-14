module

public import Oberwolfach.LongTerminalHostDensityChoices

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

/-- The level-budget bounds specialize to the exact coefficients used by
 the terminal selector, including the deeper-balance gap. -/
theorem long_terminal_level_selector_margins
    (r:ℕ) (ρ₀ rho BA δparent κmax thetaDeep eta ε xiDeep ω:ℝ)
    (hrho:ρ₀≤rho)
    (hgap:∀rho t:ℝ,ρ₀≤rho → (1/100:ℝ)/((r+4:ℕ):ℝ)≤t →
      (1+2/rho)*xiDeep≤t*ω/32)
    (hpot:δparent+δparent+
      11*((((r+4:ℕ):ℝ)+1)^4)*(2*BA/(ρ₀*((1/100:ℝ)/((r+4:ℕ):ℝ))/2)^(2*(r+4)+1))*δparent≤κmax/4)
    (hdeep:δparent+δparent+
      11*((((r+4:ℕ):ℝ)+1)^4)*(2*BA/(ρ₀*((1/100:ℝ)/((r+4:ℕ):ℝ))/2)^(2*(r+4)+1))*δparent≤thetaDeep/4)
    (hload:δparent+δparent+
      5*((((r+4:ℕ):ℝ)+1)^4)*(2*BA/(ρ₀*((1/100:ℝ)/((r+4:ℕ):ℝ))/2)^(2*(r+4)+1))*(4/ε)*δparent≤eta/4)
    (hrow:δparent+δparent≤((1/100:ℝ)/((r+4:ℕ):ℝ))/8):
    (1+2/rho)*xiDeep≤((1/100:ℝ)/((r+4:ℕ):ℝ))*ω/32 ∧
    δparent+δparent+
      11*((((r+4:ℕ):ℝ)+1)^4)*(2*BA/(ρ₀*(1/100:ℝ)/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*δparent≤κmax/4 ∧
    δparent+δparent+
      11*((((r+4:ℕ):ℝ)+1)^4)*(2*BA/(ρ₀*(1/100:ℝ)/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*δparent≤thetaDeep/4 ∧
    δparent+δparent+
      5*((((r+4:ℕ):ℝ)+1)^4)*(2*BA/(ρ₀*(1/100:ℝ)/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*δparent≤eta/4 ∧
    δparent+δparent≤((1/100:ℝ)/((r+4:ℕ):ℝ))/8 :=by
  have hid:ρ₀*((1/100:ℝ)/((r+4:ℕ):ℝ))/2=ρ₀*(1/100:ℝ)/(2*((r+4:ℕ):ℝ)):=by ring
  rw [hid] at hpot hdeep hload
  exact ⟨hgap rho ((1/100:ℝ)/((r+4:ℕ):ℝ)) hrho le_rfl,hpot,hdeep,hload,hrow⟩
end Oberwolfach
