module

public import Oberwolfach.CycleIndependentSampling

@[expose] public section
/-! A fixed test family with zero sampling mean is empty on every
positive-probability outcome of the original independent law. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {C:Type} [Fintype C] [DecidableEq C]

theorem independent_cycle_count_zero_mean
    (p:C→ℝ) (hp:∀ c,0≤p c) (hp1:∀ c,p c≤1) (A:C→Prop)
    (hzero:(∑ c,if A c then p c else 0)=0) (σ:C→Bool)
    (hσ:0<(FiniteLaw.pi (fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c))).mass σ):
    independentCycleCount A σ=0 := by
  let μ:=FiniteLaw.pi (fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c))
  have hnon:∀ ω,0 ≤ independentCycleCount A ω:=by
    intro ω;unfold independentCycleCount
    exact Finset.sum_nonneg (fun c _=>by split_ifs <;> norm_num)
  have hE:μ.expectation (independentCycleCount A)=0:=by
    rw [independent_cycle_count_expectation];exact hzero
  exact finiteLaw_nonnegative_zero_mean μ (independentCycleCount A) hnon hE σ hσ
end Oberwolfach
