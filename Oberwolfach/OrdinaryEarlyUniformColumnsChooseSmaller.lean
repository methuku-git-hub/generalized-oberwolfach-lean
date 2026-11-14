module

public import Oberwolfach.OrdinaryEarlyUniformColumnsShrinkRate

@[expose] public section
/-! Impose any later positive edit cap without changing the chosen
reservoir or moving the edit choice past the absorber sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_early_uniform_columns_choose_smaller
    (d mMatch:ℕ) (lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch α cap:ℝ)
    (hcap:0<cap)
    (hbase:OrdinaryEarlyUniformColumnsBeforeAbsorberShape d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch α):
    ∃ξedit:ℝ,0<ξedit ∧ ξedit≤cap ∧ ξedit≤bList/8 ∧ ξedit≤bMatch ∧
      OrdinaryEarlyUniformColumnsAtRate d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch α ξedit :=by
  obtain ⟨ξold,hξold,hlist,hmatch,hbase⟩:=hbase
  let ξedit:=min ξold cap
  have hpos:0<ξedit:=by dsimp [ξedit]; positivity
  have hle:ξedit≤ξold:=min_le_left _ _
  have hcap':ξedit≤cap:=min_le_right _ _
  refine ⟨ξedit,hpos,hcap',hle.trans hlist,hle.trans hmatch,?_⟩
  exact ordinary_early_uniform_columns_shrink_rate d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch α ξedit ξold hle hbase
end Oberwolfach
