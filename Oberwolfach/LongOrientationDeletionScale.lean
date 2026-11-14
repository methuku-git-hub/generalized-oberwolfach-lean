module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
/-! Choose the perturbation scale after the matching deletion threshold, and
then the host order, for the manuscript's orientation-error expression. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
open Filter
open scoped Topology
namespace Oberwolfach

theorem long_orientation_deletion_scale
    (Δ C ξmax:ℝ) (hΔ:0<Δ) (hC:0≤C) (hmax:0<ξmax):
    ∃ ξcap:ℝ,0<ξcap ∧ ξcap≤ξmax ∧ ∃ N:ℕ,∀n≥N,∀ ξ:ℝ,0≤ξ→ξ≤ξcap→
      ξ+C*Real.sqrt ξ+5*(n:ℝ)^(-(1/5:ℝ))≤Δ := by
  let a:=Δ/(4*(C+1))
  have ha:0<a:=by dsimp [a];positivity
  let ξcap:=min ξmax (min (Δ/4) (a^2))
  have hξ:0<ξcap:=by dsimp [ξcap];positivity
  have hξmax:ξcap≤ξmax:=min_le_left _ _
  have hξΔ:ξcap≤Δ/4:=(min_le_right _ _).trans (min_le_left _ _)
  have hξa:ξcap≤a^2:=(min_le_right _ _).trans (min_le_right _ _)
  have hCa:C*a≤Δ/4:=by
    have hc1:0<C+1:=by linarith
    have hc:C/(C+1)≤1:=(div_le_one hc1).2 (by linarith)
    calc
      C*a=(Δ/4)*(C/(C+1)):=by dsimp [a];field_simp [ne_of_gt hc1] <;> ring
      _≤(Δ/4)*1:=mul_le_mul_of_nonneg_left hc (by positivity)
      _=Δ/4:=by ring
  have ht:Tendsto (fun n:ℕ=>(n:ℝ)^(-(1/5:ℝ))) atTop (𝓝 0):=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/5)).comp tendsto_natCast_atTop_atTop
  have hevent:∀ᶠ n:ℕ in atTop,(n:ℝ)^(-(1/5:ℝ))<Δ/10:=
    ht.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨N,hN⟩:=Filter.eventually_atTop.1 hevent
  refine ⟨ξcap,hξ,hξmax,N,?_⟩
  intro n hn ξ hξ0 hξcap
  have hsqrt:Real.sqrt ξ≤a:=by
    have hs:=Real.sqrt_le_sqrt (hξcap.trans hξa)
    rw [Real.sqrt_sq_eq_abs,abs_of_nonneg ha.le] at hs
    exact hs
  have hmul:C*Real.sqrt ξ≤C*a:=mul_le_mul_of_nonneg_left hsqrt hC
  have hnsmall:=hN n hn
  linarith
end Oberwolfach
