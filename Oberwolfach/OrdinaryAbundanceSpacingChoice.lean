module

public import Oberwolfach.OrdinaryAbundanceCapacityCutoff

@[expose] public section
/-! Select the spacing parameter before the host and before the length
cutoff, with both the sampling spacing and path-capacity margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem ordinary_abundance_spacing_choice (θ:ℝ) (hθ:0<θ) (m:ℕ):
    ∃d:ℕ,2≤d ∧ 1/θ≤(d:ℝ) ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)<θ/2:=by
  let x:=max (1/θ) (max (64/(5*θ^2)) (20/θ))
  let d:=max 2 ⌈x⌉₊
  have hd2:2≤d:=le_max_left _ _
  have hd0:(0:ℝ)<d:=by exact_mod_cast (show 0<d by omega)
  have hx:x≤(d:ℝ):=(Nat.le_ceil x).trans (by exact_mod_cast (le_max_right 2 ⌈x⌉₊))
  have hθd:1/θ≤(d:ℝ):=(le_max_left _ _).trans hx
  have hsp:64/(5*θ^2)≤(d:ℝ):=(le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hcap:20/θ≤(d:ℝ):=(le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hsp':64≤(d:ℝ)*(5*θ^2):=(div_le_iff₀ (by positivity)).mp hsp
  have hcap':20≤(d:ℝ)*θ:=(div_le_iff₀ hθ).mp hcap
  refine ⟨d,hd2,hθd,?_,?_⟩
  · apply (div_le_iff₀ (by positivity:0<4*(d:ℝ))).2
    nlinarith only [hsp']
  · have hden:0<((m:ℝ)+1)*(d:ℝ)+5:=by positivity
    apply (div_lt_iff₀ hden).2
    have hm:0≤(m:ℝ):=by positivity
    have hmul:=mul_nonneg hm (mul_nonneg hθ.le hd0.le)
    nlinarith only [hcap',hθ,hmul]
end Oberwolfach
