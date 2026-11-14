module

public import Oberwolfach.OrdinaryDeepParentNumericHierarchy

@[expose] public section
/-! Choose the fresh-factor parameters and hub-weight bounds before the
fresh-factor theorem returns its error tolerances. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_parent_early_weights_hierarchy
    (p κe a K bcap Bmin:ℝ) (hp:0<p) (hκe:0<κe) (ha:0<a) (hK:0<K)
    (hbcap:0<bcap) (hBmin:0≤Bmin):
    ∃γ κ b B:ℝ,0<γ ∧ 0<κ ∧ 0<b ∧ b≤bcap ∧ 0<B ∧ Bmin≤B ∧
    ∀η εf:ℝ,0<η→0<εf→∃δ ε t lam:ℝ,
      OrdinaryDeepNumericParameters p κe a η εf K γ κ δ ε t lam b B :=by
  obtain ⟨γ,κ,δ₀,ε₀,t₀,lam₀,b₀,B₀,hbase⟩:=ordinary_deep_parent_numeric_hierarchy p κe a 1 1 K
    hp hκe ha (by norm_num) (by norm_num) hK
  let b:=min b₀ bcap
  let B:=max B₀ Bmin
  have hb:0<b:=lt_min hbase.b_pos hbcap
  have hbcap':b≤bcap:=min_le_right _ _
  have hB:0<B:=hbase.B_pos.trans_le (le_max_left _ _)
  have hBmin':Bmin≤B:=le_max_right _ _
  refine ⟨γ,κ,b,B,hbase.gamma_pos,hbase.kappa_pos,hb,hbcap',hB,hBmin',?_⟩
  intro η εf hη hεf
  obtain ⟨γ',κ',δ,ε,t,lam,b',B',hsmall⟩:=ordinary_deep_parent_numeric_hierarchy p κe a η εf K hp hκe ha hη hεf hK
  refine ⟨δ,ε,t,lam,?_⟩
  exact ⟨hbase.gamma_pos,hbase.kappa_pos,hsmall.delta_pos,hsmall.epsilon_pos,hsmall.t_pos,hsmall.lambda_pos,hb,hB,
    hbase.gamma_rim,hbase.kappa_rim,hbase.gamma_physical,hsmall.count_error,hsmall.lambda_conflict,hsmall.lambda_inner,
    hsmall.lambda_row,hsmall.lambda_index,hsmall.endpoint_error,(min_le_left _ _).trans hbase.lower_bound,
    hbase.upper_bound.trans (le_max_left _ _)⟩
end Oberwolfach
