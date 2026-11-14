module

public import Oberwolfach.ResidualMatchingBudgetChoices

@[expose] public section
/-! A nested choice of small errors fits the original residual capacity budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_inner_matching_budget
    (θ αCap lam η ζ ε ρ:ℝ) (d:ℕ)
    (hθ:0<θ) (hθ1:θ≤1) (hα:0<αCap) (hlam:0≤lam) (hlamθ:lam≤θ)
    (hd:0<d) (hinv:1/(d:ℝ)≤θ/1024)
    (hρ:ρ≤lam/(10*(d:ℝ))) (hρsmall:ρ≤θ/4096)
    (hη:η≤θ/4096) (hζ:ζ≤θ/4096) (hε:ε≤1/8192):
    let b:=αCap*θ/2048
    let z:=2*θ*ε+η+ζ+ρ
    z≤θ/1024 ∧
    16/(d:ℝ)+16*ρ+16*b/αCap+4*z≤θ/8:=by
  intro b z
  have hz:z≤θ/1024:=by
    have hh:=mul_le_mul_of_nonneg_left hε (le_of_lt hθ)
    dsimp [z]
    nlinarith
  have hb:b≤αCap*θ/1024:=by
    dsimp [b]
    have hh:0≤αCap*θ:=mul_nonneg hα.le hθ.le
    nlinarith
  exact ⟨hz,residual_matching_budget_of_small_parameters d hd θ αCap b lam ρ z hθ hθ1 hα hlam hlamθ hinv hρ hb hz⟩
end Oberwolfach
