module

public import Oberwolfach.OrdinaryAssignedReservoirOriginalInputs

@[expose] public section
/-! The local reserved-list margin follows from the original regular-host
degree assumption with half of its positive excess. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_host_margin
    {n D:ℕ} (P:SimpleGraph (Fin n)) (hP:P.IsRegularOfDegree D)
    (θhost α:ℝ) (hhalf:1/2≤θhost) (hα:0<α) (hdegree:(θhost+α)*(n:ℝ)≤D):
    (∀v,(1/2+α/2)*(n:ℝ)≤(P.degree v:ℝ)) ∧ (1/2:ℝ)*(n:ℝ)≤D :=by
  have hn0:(0:ℝ)≤n:=by positivity
  have hmargin:(1/2+α/2:ℝ)≤θhost+α:=by linarith
  have hlo:(1/2+α/2)*(n:ℝ)≤D:=
    (mul_le_mul_of_nonneg_right hmargin hn0).trans hdegree
  constructor
  · intro v
    simpa only [hP v] using hlo
  · nlinarith [mul_nonneg hα.le hn0]
end Oberwolfach
