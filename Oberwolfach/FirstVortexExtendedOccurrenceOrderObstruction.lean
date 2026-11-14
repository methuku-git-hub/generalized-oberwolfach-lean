module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
/-! The coarse extended-interval occurrence estimate cannot be used with
both the all-hub global-load margin and the dual-correction loss budget.
This diagnoses that proof route only; it is not a counterexample to the
original theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_extended_occurrence_order_obstruction
    (m ρ₀ rho ζ δLoss εInner δglobal:ℝ)
    (hm:1≤m) (hρ₀:ρ₀≤1) (hrho:0≤rho) (hζ:0≤ζ) (hε:0≤εInner)
    (hδ:0≤δglobal) (hLoss:5*Real.sqrt δglobal≤δLoss)
    (hSupply:rho+ζ+δLoss+εInner<ρ₀/(400*m))
    (hOccurrence:4/m≤δglobal/4):False :=by
  have hmpos:0<m:=by linarith
  have hsqrt:0≤Real.sqrt δglobal:=Real.sqrt_nonneg _
  have hδloss:0≤δLoss:=by linarith
  have hρbound:ρ₀/(400*m)≤1/(400*m):=div_le_div_of_nonneg_right hρ₀ (by positivity)
  have hsmall:δLoss<1/(400*m):=by linarith
  have hsmall':δLoss*m<1/400:=by
    have hh:δLoss*(400*m)<1:=(lt_div_iff₀ (by positivity:0<400*m)).mp hsmall
    nlinarith only [hh]
  have hlarge:16≤δglobal*m:=by
    have hh:4≤(δglobal/4)*m:=(div_le_iff₀ hmpos).mp hOccurrence
    nlinarith only [hh]
  have hsquare:25*δglobal≤δLoss^2:=by
    have heq:=Real.sq_sqrt hδ
    nlinarith [sq_nonneg (δLoss-5*Real.sqrt δglobal)]
  have hlargeSq:400≤δLoss^2*m:=by
    have hh:=mul_le_mul_of_nonneg_right hsquare hmpos.le
    nlinarith only [hh,hlarge]
  have hcompare:δLoss^2*m≤(δLoss*m)^2:=by
    have hh:0≤δLoss^2*m*(m-1):=mul_nonneg (mul_nonneg (sq_nonneg δLoss) hmpos.le) (by linarith)
    nlinarith only [hh]
  have hsmallSq:(δLoss*m)^2<1:=by
    have hnonneg:0≤δLoss*m:=mul_nonneg hδloss hmpos.le
    nlinarith [sq_nonneg (δLoss*m-1/400)]
  linarith
end Oberwolfach
