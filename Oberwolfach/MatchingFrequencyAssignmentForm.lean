module

public import Oberwolfach.LongRawContextHubFrequencies

@[expose] public section
/-! The root-load matching estimate and the component-assignment hypothesis
have the same target, with the same denominator and additive error scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem matching_frequency_assignment_form (actual θ f n r eps:ℝ)
    (h:|actual-(1-θ)*f*n/r|≤3*eps*n):
    |actual-(1-θ)*(f*n/r)|≤(3*eps)*n:=by
  convert h using 1 <;> ring
end Oberwolfach
