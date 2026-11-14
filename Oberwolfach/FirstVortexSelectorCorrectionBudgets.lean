module

public import Oberwolfach.FirstVortexEarlyDeletionRateBound
public import Oberwolfach.FirstVortexResidualTargetSize

@[expose] public section
/-! The class-matching tolerance selected by the common event and the actual
first inner vortex both fit the previously chosen correction budgets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_selector_correction_budgets
    (ρ₀ rho eta δLoss εInner ζmax lam θ eps ζ ε:ℝ) (m K:ℕ)
    (hρ:0<ρ₀) (hm:0<m) (hlam:0≤lam) (hθ:θ≤1) (hK:1≤K)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hζ:ζ≤eps/8) (hζ0:0≤ζ)
    (hlamcap:lam≤3*ζmax)
    (hbudget:∀z:ℝ,0≤z→z≤ζmax→z+δLoss<eta ∧
      rho+z+δLoss+εInner<ρ₀/(400*(m:ℝ)))
    (hε0:0≤ε) (hεcap:ε≤εInner):
    ζ+δLoss<eta ∧ rho+ζ+δLoss+εInner<ρ₀/(400*(m:ℝ)) ∧
    ∀n:ℕ,∀(U:Type) [Fintype U] (P:SimpleGraph (Fin n)) (Dv mm:ℕ) (β:ℝ)
      (Q:Vortex U P Dv β ε mm),((Q.extendedVertices 1).card:ℝ)≤εInner*n :=by
  have hζlam:=first_vortex_early_deletion_rate_bound lam θ eps ζ K hlam hθ hK heps hζ
  have hζcap:ζ≤ζmax:=by linarith
  obtain ⟨hbudget',hsupply⟩:=hbudget ζ hζ0 hζcap
  refine ⟨hbudget',hsupply,?_⟩
  intro n U _ P Dv mm β Q
  have hInner:((Q.extendedVertices 1).card:ℝ)≤ε*n:=by
    simpa only [Fintype.card_fin] using Q.first_inner_vertex_size_upper hε0
  exact hInner.trans (mul_le_mul_of_nonneg_right hεcap (by positivity))
end Oberwolfach
