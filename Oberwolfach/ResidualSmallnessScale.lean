module

public import Oberwolfach.LongSelectedListMargins

@[expose] public section
/-! A diagnostic inequality for the hypotheses of the current generic
residual-embedding theorem. It does not assert a bound on an actual residual. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem residual_smallness_forces_quadratic_scale
    (θ β δ:ℝ) (hθ:0<θ) (hθ1:θ≤1) (hβ:0≤β) (hβθ:β≤θ)
    (hδ:δ≤(β/100)^2):
    δ≤θ^2/10000 ∧ δ<θ:=by
  have hsq:β^2≤θ^2:=by nlinarith
  constructor
  · nlinarith
  · have hθsq:θ^2≤θ:=by nlinarith
    nlinarith
end Oberwolfach
