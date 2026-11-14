module

public import Oberwolfach.OrdinaryDeepParentMargins

@[expose] public section
/-! Choose a compatible strict hierarchy for the numerical deep-parent
    requirements before the graph and the later cleanup are selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach

structure OrdinaryDeepNumericParameters
    (p κe a η εf K γ κ δ ε t lam b B:ℝ) : Prop where
  gamma_pos : 0<γ
  kappa_pos : 0<κ
  delta_pos : 0<δ
  epsilon_pos : 0<ε
  t_pos : 0<t
  lambda_pos : 0<lam
  b_pos : 0<b
  B_pos : 0<B
  gamma_rim : γ≤(p^4/16)*a
  kappa_rim : κ≤(p^4/16)*a
  gamma_physical : γ*K≤endpointCountCoefficient p κe
  count_error : ε≤min (p^4/16) (p^3/2)
  lambda_conflict : lam≤εf
  lambda_inner : lam≤1/24
  lambda_row : 4*lam≤ε/2
  lambda_index : 3*lam≤ε*κe/2
  endpoint_error : δ+(2*40+(1+2*40)/(2*κe*p))*lam+(t+10*(40/(κe*p^5))*lam)≤η
  lower_bound : b≤1/30
  upper_bound : (40/(κe*p^5))*K^2≤B

theorem ordinary_deep_parent_numeric_hierarchy
    (p κe a η εf K:ℝ) (hp:0<p) (hκe:0<κe) (ha:0<a) (hη:0<η) (hεf:0<εf) (hK:0<K) :
    ∃ γ κ δ ε t lam b B:ℝ, OrdinaryDeepNumericParameters p κe a η εf K γ κ δ ε t lam b B := by
  let coeff:=endpointCountCoefficient p κe
  let C1:ℝ:=2*40+(1+2*40)/(2*κe*p)
  let C2:ℝ:=10*(40/(κe*p^5))
  let ε:ℝ:=min (p^4/16) (p^3/2)/2
  have hcoeff:0<coeff:=endpointCountCoefficient_pos p κe hp hκe
  have hC1:0<C1:=by dsimp [C1];positivity
  have hC2:0<C2:=by dsimp [C2];positivity
  have hε:0<ε:=by dsimp [ε];positivity
  let γ:ℝ:=min ((p^4/16)*a) (coeff/K)/2
  let κ:ℝ:=((p^4/16)*a)/2
  let δ:ℝ:=η/8
  let t:ℝ:=η/8
  let lam:ℝ:=min (1/24) (min εf (min (ε/8) (min (ε*κe/6) (η/(4*(C1+C2+1))))))/2
  let b:ℝ:=1/60
  let B:ℝ:=(40/(κe*p^5))*K^2+1
  have hγ:0<γ:=by dsimp [γ];positivity
  have hκ:0<κ:=by dsimp [κ];positivity
  have hδ:0<δ:=by dsimp [δ];positivity
  have ht:0<t:=by dsimp [t];positivity
  have hlam:0<lam:=by dsimp [lam];positivity
  have hb:0<b:=by dsimp [b];norm_num
  have hB:0<B:=by dsimp [B];positivity
  have hγ1:γ≤(p^4/16)*a := by
    have hh:=min_le_left ((p^4/16)*a) (coeff/K)
    dsimp [γ]
    have hp' : 0≤(p^4/16)*a := by positivity
    linarith
  have hγ2:γ*K≤coeff := by
    have hh:=min_le_right ((p^4/16)*a) (coeff/K)
    have hc0:0≤coeff/K:=by positivity
    have hsmall:γ≤coeff/K:=by dsimp [γ];linarith
    have hmul:=mul_le_mul_of_nonneg_right hsmall hK.le
    have heq:(coeff/K)*K=coeff:=by field_simp
    rw [heq] at hmul
    exact hmul
  have hκ1:κ≤(p^4/16)*a:=by
    have hh:0≤(p^4/16)*a:=by positivity
    dsimp [κ];linarith
  have hε1:ε≤min (p^4/16) (p^3/2):=by
    have hh:0≤min (p^4/16) (p^3/2):=by positivity
    dsimp [ε];linarith
  have hlam1:lam≤1/24:=by
    have hh:=min_le_left (1/24:ℝ) (min εf (min (ε/8) (min (ε*κe/6) (η/(4*(C1+C2+1))))))
    dsimp only [lam]
    linarith
  have hlam2:lam≤εf:=by
    have hh : min (1/24:ℝ) (min εf (min (ε/8) (min (ε*κe/6) (η/(4*(C1+C2+1)))))) ≤ εf := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    dsimp only [lam]
    linarith
  have hlam3:4*lam≤ε/2:=by
    have hh : min (1/24:ℝ) (min εf (min (ε/8) (min (ε*κe/6) (η/(4*(C1+C2+1)))))) ≤ ε/8 := by
      exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_left _ _)
    dsimp only [lam]
    linarith
  have hlam4:3*lam≤ε*κe/2:=by
    have hh : min (1/24:ℝ) (min εf (min (ε/8) (min (ε*κe/6) (η/(4*(C1+C2+1)))))) ≤ ε*κe/6 := by
      exact le_trans (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_right _ _)) (min_le_left _ _)
    have hprod:0≤ε*κe:=mul_nonneg hε.le hκe.le
    dsimp only [lam]
    nlinarith only [hh,hprod]
  have hlam5:lam≤η/(4*(C1+C2+1)):=by
    have hh : min (1/24:ℝ) (min εf (min (ε/8) (min (ε*κe/6) (η/(4*(C1+C2+1)))))) ≤ η/(4*(C1+C2+1)) := by
      exact le_trans (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_right _ _)) (min_le_right _ _)
    have hnonneg:0≤η/(4*(C1+C2+1)):=by positivity
    dsimp only [lam]
    linarith
  have hsum:δ+C1*lam+(t+C2*lam)≤η:=by
    have hh:lam*(4*(C1+C2+1))≤η:=(le_div_iff₀ (by positivity)).mp hlam5
    dsimp only [δ,t]
    nlinarith [mul_nonneg hlam.le hC1.le, mul_nonneg hlam.le hC2.le]
  refine ⟨γ,κ,δ,ε,t,lam,b,B,⟨hγ,hκ,hδ,hε,ht,hlam,hb,hB,hγ1,hκ1,?_,hε1,hlam2,hlam1,hlam3,hlam4,?_,?_,?_⟩⟩
  · simpa only [coeff] using hγ2
  · simpa only [C1,C2] using hsum
  · dsimp [b];norm_num
  · dsimp [B];linarith
end Oberwolfach
