module

public import Oberwolfach.OrdinaryReservedHierarchyErrorRates
public import Oberwolfach.OrdinaryTrackedComplementBudgetEventually

@[expose] public section
/-! The reserved matching hierarchy supplies every small-rate hypothesis for
the physical discrepancy of its own tracked complement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_placement_tracked_cost_bound
    (m d tAbs aAbs bAbs:ℕ) (η δ θ κ κ' a γ b σ:ℝ)
    (hη:0<η) (hδ:0<δ) (hδ1:δ≤1) (hcap:5*Real.sqrt δ≤η)
    (hθ:0<θ) (hθδ:θ≤δ/8) (hκ:0<κ) (hκ'κ:κ'≤κ)
    (ha:a≤κ') (hγ:γ≤κ') (hb:b≤δ/8) (hσ:σ≤η)
    (hsize:2*θ+δ/8+((m:ℝ)+2)*κ≤δ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀unused edit rows hubs:ℝ,
    unused≤2*θ→edit≤σ*n→
    rows+hubs≤((2^(tAbs*tAbs)*aAbs+2^(tAbs*tAbs)*bAbs:ℕ):ℝ)→
    let LF:ℝ:=2*((3*d:ℕ):ℝ)
    let newLoss:ℝ:=5*Real.sqrt δ*n
    let κref:ℝ:=(max a γ)*n+unused*n+3*(n:ℝ)^(3/5:ℝ)+((6*d+4:ℕ):ℝ)+b*n+LF
    let e:ℝ:=σ*n+2*(σ*n)+LF
    let Lrim:ℝ:=edit+κref+newLoss
    let Lspoke:ℝ:=max (2*newLoss+(Lrim+e)/2) (2*(δ*n)+σ*n);
    Lrim+Lspoke+rows+hubs≤14*η*n :=by
  obtain ⟨_,hκrate,hdel,_⟩:=ordinary_reserved_hierarchy_error_rates m δ θ κ κ' a γ b η
    hδ hδ1 hcap hθ hθδ hκ hκ'κ ha hγ hb hsize
  obtain ⟨N,hN⟩:=ordinary_tracked_complement_budget_eventually d tAbs aAbs bAbs η δ θ (max a γ) b σ
    hη hδ.le hδ1 hcap hθδ hκrate hdel hσ
  refine ⟨N,?_⟩
  intro n hn unused edit rows hubs hunused hedit hrows LF newLoss κref e Lrim Lspoke
  have hedit':edit≤η*n:=hedit.trans (mul_le_mul_of_nonneg_right hσ (by positivity))
  exact hN n hn unused edit rows hubs hunused hedit' hrows
end Oberwolfach
