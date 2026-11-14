module

public import Oberwolfach.OrdinaryDeepParentNumericScale
public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy

@[expose] public section
/-! The deep parent and triangle root-first construction can use the same
four small numerical parameters after the row tolerance is known. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_inner_numeric_of_deep
    (p κe a η εf K γ κ δ ε t lam b B εrows:ℝ)
    (h:OrdinaryDeepNumericParameters p κe a η εf K γ κ δ ε t lam b B)
    (hrows:ε≤εrows):
    OrdinaryTriangleInnerNumericParameters p κe εf η εrows δ ε t lam :=by
  exact ⟨h.delta_pos,h.epsilon_pos,h.t_pos,h.lambda_pos,hrows,h.count_error,
    h.lambda_conflict,h.lambda_inner,h.lambda_row,h.lambda_index,h.endpoint_error⟩

theorem ordinary_triangle_deep_inner_common_numeric
    (p κe a η εf K γ κ δ ε t lam b B εrows:ℝ)
    (hη:0≤η) (hrows:0<εrows)
    (h:OrdinaryDeepNumericParameters p κe a η εf K γ κ δ ε t lam b B):
    ∃δ' ε' t' lam':ℝ,
      OrdinaryDeepNumericParameters p κe a η εf K γ κ δ' ε' t' lam' b B ∧
      OrdinaryTriangleInnerNumericParameters p κe εf η εrows δ' ε' t' lam' :=by
  obtain ⟨δ',ε',t',lam',_,he,_,_,hdeep⟩:=
    ordinary_deep_parent_numeric_cap p κe a η εf K γ κ δ ε t lam b B εrows hη hrows h
  exact ⟨δ',ε',t',lam',hdeep,
    ordinary_triangle_inner_numeric_of_deep p κe a η εf K γ κ δ' ε' t' lam' b B εrows hdeep he⟩
theorem ordinary_triangle_deep_inner_numeric_hierarchy
    (p κe a η εf K εrows:ℝ) (hp:0<p) (hκe:0<κe) (ha:0<a) (hη:0<η)
    (hεf:0<εf) (hK:0<K) (hrows:0<εrows):
    ∃γ κ δ ε t lam b B:ℝ,
      OrdinaryDeepNumericParameters p κe a η εf K γ κ δ ε t lam b B ∧
      OrdinaryTriangleInnerNumericParameters p κe εf η εrows δ ε t lam :=by
  obtain ⟨γ,κ,δ,ε,t,lam,b,B,h⟩:=ordinary_deep_parent_numeric_hierarchy p κe a η εf K hp hκe ha hη hεf hK
  obtain ⟨δ',ε',t',lam',hdeep,hinner⟩:=
    ordinary_triangle_deep_inner_common_numeric p κe a η εf K γ κ δ ε t lam b B εrows hη.le hrows h
  exact ⟨γ,κ,δ',ε',t',lam',b,B,hdeep,hinner⟩
end Oberwolfach
