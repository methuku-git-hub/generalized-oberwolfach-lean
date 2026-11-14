module

public import Oberwolfach.ResidualMatchingBudgetChoices

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_residual_matching_alpha_choice
    (αold b ρ₀ θ:ℝ) (hαold:0<αold) (hρ₀:0<ρ₀) (hθ:0<θ)
    (hαb:αold/16≤b):
    ∃α:ℝ,0<α ∧ α≤αold ∧ α/16≤b ∧
      α/16≤((ρ₀/4)/40000)*θ/1024 :=by
  let α:ℝ:=min αold (((ρ₀/4)/40000)*θ/64)
  have hα:0<α:=by dsimp [α];positivity
  have hle:α≤αold:=min_le_left _ _
  have hsmall:α≤((ρ₀/4)/40000)*θ/64:=min_le_right _ _
  exact ⟨α,hα,hle,by linarith,by linarith⟩

theorem first_vortex_residual_matching_budget
    (d:ℕ) (hd:0<d) (θ ρ₀ α lam a γ z:ℝ) (hθ:0<θ) (hθ1:θ≤1)
    (hρ₀:0<ρ₀) (hlam:0≤lam) (hlamθ:lam≤θ)
    (hinv:1/(d:ℝ)≤θ/1024) (ha:a≤lam/(10*(d:ℝ)))
    (hγ:γ≤lam/(10*(d:ℝ))) (hα:α/16≤((ρ₀/4)/40000)*θ/1024)
    (hz:z≤θ/1024):
    16/(d:ℝ)+16*max a γ+16*(α/16)/((ρ₀/4)/40000)+4*z≤θ/8:=by
  have hcap:0<((ρ₀/4)/40000):=by positivity
  exact residual_matching_budget_of_small_parameters d hd θ ((ρ₀/4)/40000) (α/16) lam (max a γ) z hθ hθ1 hcap hlam hlamθ hinv (max_le ha hγ) hα hz
end Oberwolfach
