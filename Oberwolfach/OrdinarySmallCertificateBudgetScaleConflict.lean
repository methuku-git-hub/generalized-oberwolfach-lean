module

public import Oberwolfach.OrdinaryPlacementStage

@[expose] public section
/-! A small certificate budget can make the placement tolerance much
smaller than the vortex scale; this rules out one proposed ordering shortcut. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_small_certificate_budget_scale_conflict
    (ε η cap δ ζ:ℝ) (hε:0<ε) (hε1:ε≤1) (hη:0≤η) (hδ:0≤δ)
    (hζ:ζ≤1) (hbudget:15*η≤ζ*ε/2) (hcap:cap≤η) (hsqrt:5*Real.sqrt δ≤cap):
    δ<2*ε :=by
  have hs:0≤Real.sqrt δ:=Real.sqrt_nonneg _
  have hζε:ζ*ε≤ε:=by
    have hh:=mul_le_mul_of_nonneg_right hζ hε.le
    simpa using hh
  have hsε:Real.sqrt δ≤ε/150:=by linarith
  have hsone:Real.sqrt δ≤1:=by linarith
  have hsquare:(Real.sqrt δ)^2≤Real.sqrt δ:=by
    have hh:=mul_nonneg hs (sub_nonneg.mpr hsone)
    nlinarith
  have hδsmall:δ≤Real.sqrt δ:=by nlinarith [Real.sq_sqrt hδ]
  linarith
end Oberwolfach
