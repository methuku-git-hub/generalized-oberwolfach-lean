module

public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy

@[expose] public section
/-! Small relative conflict, edit and sampling errors discharge the numeric
hypotheses of the inner triangle cleanup on the actual inner sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_inner_numeric_inputs_from_scales
    (p κe εfactor ηend εrows δ εcount t lam A Z L Ledit tR tH tP δactual:ℝ)
    (num:OrdinaryTriangleInnerNumericParameters p κe εfactor ηend εrows δ εcount t lam)
    (hp:0<p) (hκ:0<κe) (hA:0<A) (hZ:κe*A≤Z)
    (hL:0≤L) (hLs:L≤lam*A) (hE:0≤Ledit) (hEs:Ledit≤lam*A)
    (hR:tR≤εcount*A/2) (hH:tH≤εcount*Z/2) (hP:tP≤t) (hδ:δactual≤δ):
    tR+4*Ledit≤εcount*A ∧ tH+3*Ledit≤εcount*Z ∧
    L≤A/24 ∧ L≤εfactor*A ∧
    δactual+(2*40+(1+2*40)/(2*κe*p))*L/A+
      (tP+10*(40/(κe*p^5))*Ledit/A)≤ηend:=by
  have hC1:0≤(2*40+(1+2*40)/(2*κe*p):ℝ):=by positivity
  have hC2:0≤(10*(40/(κe*p^5)):ℝ):=by positivity
  have hLratio:L/A≤lam:=(div_le_iff₀ hA).2 (by simpa [mul_comm] using hLs)
  have hEratio:Ledit/A≤lam:=(div_le_iff₀ hA).2 (by simpa [mul_comm] using hEs)
  have hrow:tR+4*Ledit≤εcount*A:=by
    have h1:=mul_le_mul_of_nonneg_left hEs (show (0:ℝ)≤4 by norm_num)
    have h2:=mul_le_mul_of_nonneg_right num.lambda_row hA.le
    nlinarith only [hR,h1,h2]
  have hindex:tH+3*Ledit≤εcount*Z:=by
    have h1:=mul_le_mul_of_nonneg_left hEs (show (0:ℝ)≤3 by norm_num)
    have h2:=mul_le_mul_of_nonneg_right num.lambda_index hA.le
    have h3:=mul_le_mul_of_nonneg_left hZ num.count_pos.le
    nlinarith only [hH,h1,h2,h3]
  have hinner:L≤A/24:=by
    calc
      L≤lam*A:=hLs
      _≤(1/24:ℝ)*A:=mul_le_mul_of_nonneg_right num.lambda_inner hA.le
      _=A/24:=by ring
  have hfactor:L≤εfactor*A:=hLs.trans (mul_le_mul_of_nonneg_right num.lambda_conflict hA.le)
  have h1:(2*40+(1+2*40)/(2*κe*p))*L/A≤(2*40+(1+2*40)/(2*κe*p))*lam:=by
    convert mul_le_mul_of_nonneg_left hLratio hC1 using 1 <;> ring
  have h2:10*(40/(κe*p^5))*Ledit/A≤10*(40/(κe*p^5))*lam:=by
    convert mul_le_mul_of_nonneg_left hEratio hC2 using 1 <;> ring
  exact ⟨hrow,hindex,hinner,hfactor,by linarith only [h1,h2,hP,hδ,num.endpoint_error]⟩
end Oberwolfach
