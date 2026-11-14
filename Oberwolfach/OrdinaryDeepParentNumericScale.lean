module

public import Oberwolfach.OrdinaryDeepParentNumericHierarchy

@[expose] public section
/-! Scale down the later parent errors together, preserving the already
    chosen factor parameters and weight bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_parent_numeric_scale
    (p κe a η εf K γ κ δ ε t lam b B s:ℝ)
    (hη:0≤η) (hs:0<s) (hs1:s≤1)
    (h:OrdinaryDeepNumericParameters p κe a η εf K γ κ δ ε t lam b B):
    OrdinaryDeepNumericParameters p κe a η εf K γ κ (s*δ) (s*ε) (s*t) (s*lam) b B :=by
  have hsε:s*ε≤ε:=by nlinarith [h.epsilon_pos]
  have hslam:s*lam≤lam:=by nlinarith [h.lambda_pos]
  have hrow:=mul_le_mul_of_nonneg_left h.lambda_row hs.le
  have hindex:=mul_le_mul_of_nonneg_left h.lambda_index hs.le
  have hend:=mul_le_mul_of_nonneg_left h.endpoint_error hs.le
  have hsη:s*η≤η:=by nlinarith
  refine ⟨h.gamma_pos,h.kappa_pos,mul_pos hs h.delta_pos,mul_pos hs h.epsilon_pos,
    mul_pos hs h.t_pos,mul_pos hs h.lambda_pos,h.b_pos,h.B_pos,h.gamma_rim,h.kappa_rim,
    h.gamma_physical,hsε.trans h.count_error,hslam.trans h.lambda_conflict,hslam.trans h.lambda_inner,?_,?_,?_,h.lower_bound,h.upper_bound⟩
  · nlinarith only [hrow]
  · nlinarith only [hindex]
  · have heq:s*δ+(2*40+(1+2*40)/(2*κe*p))*(s*lam)+
        (s*t+10*(40/(κe*p^5))*(s*lam))=
        s*(δ+(2*40+(1+2*40)/(2*κe*p))*lam+(t+10*(40/(κe*p^5))*lam)):=by ring
    rw [heq]
    exact hend.trans hsη

theorem ordinary_deep_parent_numeric_cap
    (p κe a η εf K γ κ δ ε t lam b B cap:ℝ)
    (hη:0≤η) (hcap:0<cap)
    (h:OrdinaryDeepNumericParameters p κe a η εf K γ κ δ ε t lam b B):
    ∃δ' ε' t' lam':ℝ,δ'≤cap ∧ ε'≤cap ∧ t'≤cap ∧ lam'≤cap ∧
      OrdinaryDeepNumericParameters p κe a η εf K γ κ δ' ε' t' lam' b B :=by
  let total:ℝ:=1+δ+ε+t+lam
  have htotal:0<total:=by dsimp [total];positivity [h.delta_pos,h.epsilon_pos,h.t_pos,h.lambda_pos]
  let s:ℝ:=min (1/2) (cap/(2*total))
  have hs:0<s:=by dsimp [s];positivity
  have hs1:s≤1:=by dsimp [s];have hh:=min_le_left (1/2:ℝ) (cap/(2*total));linarith
  have hscap:s≤cap/(2*total):=min_le_right _ _
  have hmul:s*(2*total)≤cap:=(le_div_iff₀ (by positivity : 0<2*total)).mp hscap
  have hbound:s*total≤cap:=by nlinarith
  have hd:δ≤total:=by dsimp [total];linarith [h.epsilon_pos,h.t_pos,h.lambda_pos]
  have he:ε≤total:=by dsimp [total];linarith [h.delta_pos,h.t_pos,h.lambda_pos]
  have ht:t≤total:=by dsimp [total];linarith [h.delta_pos,h.epsilon_pos,h.lambda_pos]
  have hl:lam≤total:=by dsimp [total];linarith [h.delta_pos,h.epsilon_pos,h.t_pos]
  refine ⟨s*δ,s*ε,s*t,s*lam,?_,?_,?_,?_,ordinary_deep_parent_numeric_scale p κe a η εf K γ κ δ ε t lam b B s hη hs hs1 h⟩
  · exact (mul_le_mul_of_nonneg_left hd hs.le).trans hbound
  · exact (mul_le_mul_of_nonneg_left he hs.le).trans hbound
  · exact (mul_le_mul_of_nonneg_left ht hs.le).trans hbound
  · exact (mul_le_mul_of_nonneg_left hl hs.le).trans hbound
end Oberwolfach
