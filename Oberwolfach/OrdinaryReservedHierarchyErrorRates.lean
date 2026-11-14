module

public import Oberwolfach.OrdinaryTrackedComplementCostBudget

@[expose] public section
/-! The already chosen placement hierarchy gives the row, deletion and
unused-colour rates required by the actual-complement edit budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_reserved_hierarchy_error_rates
    (m:ℕ) (δ θ κ κ' a γ b η:ℝ)
    (hδ:0<δ) (hδ1:δ≤1) (hcap:5*Real.sqrt δ≤η)
    (hθ:0<θ) (hθδ:θ≤δ/8) (hκ:0<κ) (hκ'κ:κ'≤κ)
    (ha:a≤κ') (hγ:γ≤κ') (hb:b≤δ/8)
    (hsize:2*θ+δ/8+((m:ℝ)+2)*κ≤δ):
    δ≤η ∧ max a γ≤δ ∧ b≤δ ∧ 2*θ≤δ :=by
  have hδeta:=ordinary_sqrt_cap_controls_residual_rate δ η hδ.le hδ1 hcap
  have hm:0≤(m:ℝ)+1:=by positivity
  have hκδ:κ≤δ:=by nlinarith [mul_nonneg hm hκ.le]
  refine ⟨hδeta,max_le (ha.trans (hκ'κ.trans hκδ)) (hγ.trans (hκ'κ.trans hκδ)),?_,?_⟩ <;> linarith
end Oberwolfach
