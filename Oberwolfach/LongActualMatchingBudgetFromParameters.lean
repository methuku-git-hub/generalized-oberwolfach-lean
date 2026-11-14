module

public import Oberwolfach.LongMatchingErrorBudget
public import Oberwolfach.LongInnerMatchingBudget

@[expose] public section
/-! The actual matching choices meet the residual capacity budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_actual_matching_budget_from_parameters
    (θ αCap lam eps η ζ ε:ℝ) (d K:ℕ)
    (hθ:0<θ) (hθ1:θ≤1) (hα:0<αCap) (hlam:0≤lam) (hlamθ:lam≤θ)
    (hd:0<d) (hK:5≤K) (hinv:1/(d:ℝ)≤θ/1024)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hη:η≤θ/4096) (hζ:ζ≤θ/4096) (hε:ε≤1/8192):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    let b:=αCap*θ/2048
    let z:=2*θ*ε+η+ζ+max a γ
    z≤θ/1024 ∧
      16/(d:ℝ)+16*max a γ+16*b/αCap+4*z≤θ/8:=by
  intro a γ b z
  have hlam1:lam≤1:=le_trans hlamθ hθ1
  have hsmall:max a γ≤θ/4096:=long_matching_error_budget lam θ eps d K hlam hlam1 hθ.le hK heps
  have had:a≤lam/(10*(d:ℝ)):=min_le_left _ _
  have hgd:γ≤lam/(10*(d:ℝ)):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ:max a γ≤lam/(10*(d:ℝ)):=max_le had hgd
  exact long_inner_matching_budget θ αCap lam η ζ ε (max a γ) d hθ hθ1 hα hlam hlamθ hd hinv hρ hsmall hη hζ hε
end Oberwolfach
