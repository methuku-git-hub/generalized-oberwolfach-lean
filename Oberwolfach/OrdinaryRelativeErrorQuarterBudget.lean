module

public import Oberwolfach.OrdinaryUnreservedResidualQuarterFromMatching

@[expose] public section
/-! A simple hierarchy for the relative test and matching errors supplies the
small error required by the unreserved residual lower bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_relative_error_quarter_budget
    (θ lam γ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (hlam:0≤lam) (hγ:0≤γ)
    (hlamSmall:lam≤θ/10) (hγSmall:γ≤lam/10):
    0≤lam+γ*(1-θ+lam) ∧ lam+γ*(1-θ+lam)≤θ/8 :=by
  have hfac0:0≤1-θ+lam:=by linarith
  have hfac1:1-θ+lam≤1:=by linarith
  have hgθ:γ≤θ/100:=by linarith
  have hh:=mul_le_mul_of_nonneg_left hfac1 hγ
  constructor
  · positivity
  · nlinarith
end Oberwolfach
