module

public import Oberwolfach.OrdinaryProportionalReserveBalance

@[expose] public section
/-! Bound the imbalance of a sampled reserve from its mean and deviation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_reserve_imbalance_bound (A D τ c e:ℝ) (hτ:0≤τ)
    (hd:|D|≤c) (he:|A-τ*D|≤e):|A|≤τ*c+e:=by
  have hmul:|τ*D|≤τ*c:=by rw [abs_mul,abs_of_nonneg hτ];exact mul_le_mul_of_nonneg_left hd hτ
  have ht:|A|≤|A-τ*D|+|τ*D|:=by
    have hh:=abs_add_le (A-τ*D) (τ*D)
    convert hh using 1 <;> congr 1 <;> ring
  linarith only [he,hmul,ht]
end Oberwolfach
