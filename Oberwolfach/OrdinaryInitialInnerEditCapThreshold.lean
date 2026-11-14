module

public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy

@[expose] public section
/-! Once the inner-event edit cap is known, a terminal-size threshold makes
the deterministic initial conflict and correction edit fit that cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_initial_inner_edit_cap_threshold (d:ℕ) (cap:ℝ) (hcap:0<cap):
    ∃M:ℕ,1≤M ∧ ∀(ε δcap:ℝ) (I B:ℕ),
      0≤ε→0≤δcap→δcap≤cap/2→(M:ℝ)≤(1-ε)*I→
      0≤2*((3*d:ℕ):ℝ)+δcap*min (I:ℝ) B ∧
        2*((3*d:ℕ):ℝ)+δcap*min (I:ℝ) B≤cap*I :=by
  obtain ⟨M₀,hM₀⟩:=exists_nat_gt (2*(2*((3*d:ℕ):ℝ))/cap)
  let M:=max 1 M₀
  have hM:2*(2*((3*d:ℕ):ℝ))/cap<(M:ℝ):=by
    exact lt_of_lt_of_le hM₀ (by exact_mod_cast le_max_right 1 M₀)
  have hMcap:= (div_lt_iff₀ hcap).mp hM
  refine ⟨M,le_max_left _ _,?_⟩
  intro ε δcap I B hε hδ hδcap hsize
  have hI:(M:ℝ)≤I:=by
    have hh:0≤ε*(I:ℝ):=by positivity
    nlinarith only [hsize,hh]
  have hconflict:2*((3*d:ℕ):ℝ)≤(cap/2)*I:=by
    have hh:=mul_le_mul_of_nonneg_left hI hcap.le
    nlinarith only [hMcap,hh]
  have hmin:min (I:ℝ) B≤I:=min_le_left _ _
  have hterm:δcap*min (I:ℝ) B≤(cap/2)*I:=by
    exact (mul_le_mul_of_nonneg_left hmin hδ).trans
      (mul_le_mul_of_nonneg_right hδcap (by positivity))
  constructor
  · positivity
  · nlinarith only [hconflict,hterm]
end Oberwolfach
