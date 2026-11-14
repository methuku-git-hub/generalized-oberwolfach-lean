module

public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy

@[expose] public section
/-! The root scale may be chosen later and smaller than the early inner
numeric allowance, without changing any of the other selected tolerances. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_inner_numeric_smaller_root
    (p κe εfactor ηend εrows δ εcount t lam lam':ℝ)
    (hp:0<p) (hκ:0<κe)
    (hnum:OrdinaryTriangleInnerNumericParameters p κe εfactor ηend εrows δ εcount t lam)
    (hlam':0<lam') (hsmall:lam'≤lam):
    OrdinaryTriangleInnerNumericParameters p κe εfactor ηend εrows δ εcount t lam' :=by
  have hC1:0≤2*40+(1+2*40)/(2*κe*p):=by positivity
  have hC2:0≤10*(40/(κe*p^5)):=by positivity
  have h1:=mul_le_mul_of_nonneg_left hsmall hC1
  have h2:=mul_le_mul_of_nonneg_left hsmall hC2
  exact ⟨hnum.delta_pos,hnum.count_pos,hnum.t_pos,hlam',hnum.count_rows,hnum.count_geometry,
    hsmall.trans hnum.lambda_conflict,hsmall.trans hnum.lambda_inner,
    by linarith [hnum.lambda_row],by linarith [hnum.lambda_index],
    by linarith [hnum.endpoint_error]⟩
end Oberwolfach
