module

public import Oberwolfach.CycleSamplingLargeTail

@[expose] public section
/-! Pointwise numerical estimates for relative degree tails and large
codegree tails of the fixed independent cycle sample. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem cycle_sampling_relative_tail_bound
    (θ m c n:ℝ)
    (hmean:c*n^2≤θ^2*m/3):
    2*Real.exp (-θ^2*m/3)≤2*Real.exp (-c*n^2):=by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  linarith

theorem cycle_sampling_large_tail_half
    (m t:ℝ) (hm:0<m) (ht:0<t) (hhalf:Real.exp 1*m/t≤1/2):
    (Real.exp 1*m/t)^t≤Real.exp (-(Real.log 2)*t):=by
  have hbase:0<Real.exp 1*m/t:=by positivity
  have hpow:(Real.exp 1*m/t)^t≤(1/2:ℝ)^t:=
    Real.rpow_le_rpow hbase.le hhalf ht.le
  have heq:(1/2:ℝ)^t=Real.exp (-(Real.log 2)*t):=by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<1/2)]
    congr 1
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
  exact hpow.trans_eq heq
end Oberwolfach
