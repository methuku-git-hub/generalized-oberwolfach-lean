module

public import Oberwolfach.LongResidualCapacityFromInnerTarget
public import Oberwolfach.PartitionMargins

@[expose] public section
/-! The sublinear term in the matching-capacity estimate is eventually small. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_residual_capacity_sublinear_error
    (θ:ℝ) (hθ:0<θ) (d:ℕ) (hd:0<d):
    ∃N:ℕ,∀n:ℕ,N≤n→32*(n:ℝ)^(3/4:ℝ)/(d:ℝ)+18≤θ*n/8:=by
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (θ/256) (18/32) (by positivity)
  refine ⟨N,?_⟩
  intro n hn
  have hdR:1≤(d:ℝ):=by exact_mod_cast hd
  have hpow:0≤(n:ℝ)^(3/4:ℝ):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hdiv:32*(n:ℝ)^(3/4:ℝ)/(d:ℝ)≤32*(n:ℝ)^(3/4:ℝ):=by
    apply (div_le_iff₀ (by positivity : 0<(d:ℝ))).2
    nlinarith
  have hh:=hN n hn
  nlinarith
end Oberwolfach
