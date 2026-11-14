module

public import Oberwolfach.OrdinaryDeepParentNumericScale
public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy

@[expose] public section
/-! The deep-parent and inner triangle hierarchies can use exactly the
selected row tolerance once it is below the original geometric bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_deep_inner_exact_rows_hierarchy
    (p κe a η εf K εrows:ℝ) (hp:0<p) (hκe:0<κe) (ha:0<a) (hη:0<η)
    (hεf:0<εf) (hK:0<K) (hrows:0<εrows)
    (hrowsGeom:εrows≤min (p^4/16) (p^3/2)):
    ∃γ κ δ t lam b B:ℝ,
      OrdinaryDeepNumericParameters p κe a η εf K γ κ δ εrows t lam b B ∧
      OrdinaryTriangleInnerNumericParameters p κe εf η εrows δ εrows t lam :=by
  obtain ⟨γ,κ,δ,ε,t,lam,b,B,h⟩:=ordinary_deep_parent_numeric_hierarchy p κe a η εf K hp hκe ha hη hεf hK
  obtain ⟨δ',ε',t',lam',_,he,_,_,hdeep⟩:=
    ordinary_deep_parent_numeric_cap p κe a η εf K γ κ δ ε t lam b B εrows hη.le hrows h
  have hindex:=mul_le_mul_of_nonneg_right he hκe.le
  have hdeep':OrdinaryDeepNumericParameters p κe a η εf K γ κ δ' εrows t' lam' b B:=by
    refine ⟨hdeep.gamma_pos,hdeep.kappa_pos,hdeep.delta_pos,hrows,hdeep.t_pos,hdeep.lambda_pos,
      hdeep.b_pos,hdeep.B_pos,hdeep.gamma_rim,hdeep.kappa_rim,hdeep.gamma_physical,hrowsGeom,
      hdeep.lambda_conflict,hdeep.lambda_inner,?_,?_,hdeep.endpoint_error,hdeep.lower_bound,hdeep.upper_bound⟩
    · linarith [hdeep.lambda_row]
    · nlinarith only [hdeep.lambda_index,hindex]
  refine ⟨γ,κ,δ',t',lam',b,B,hdeep',?_⟩
  exact ⟨hdeep'.delta_pos,hrows,hdeep'.t_pos,hdeep'.lambda_pos,le_rfl,hdeep'.count_error,
    hdeep'.lambda_conflict,hdeep'.lambda_inner,hdeep'.lambda_row,hdeep'.lambda_index,hdeep'.endpoint_error⟩
end Oberwolfach
