module

public import Oberwolfach.OrdinaryCertificateFitsDeepInputs

@[expose] public section
/-! Compatibility of the selected parent-reference reserve with the two
geometric losses of the local wheel certificate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_certificate_reference_margin
    (h ζparent geomCap ξreserve ζout:ℝ)
    (hζ:ζparent ≤ h) (hcap:2*geomCap ≤ h/2)
    (hξ:ξreserve ≤ geomCap) (hout:ζout ≤ geomCap):
    h/2 ≤ (2*h-ζparent)-ξreserve-ζout :=by
  linarith

theorem ordinary_deep_certificate_cleanup_boundaries
    (eParent hParent cBoundary ε βe βh:ℝ)
    (he:0 ≤ eParent) (hh:0 ≤ hParent) (hε:0 ≤ ε)
    (heBound:eParent ≤ cBoundary) (hhBound:hParent ≤ cBoundary)
    (heq:βe=(eParent/2)*ε) (heq':βh=(hParent/2)*ε):
    0 ≤ βe ∧ βe ≤ cBoundary*ε ∧ 0 ≤ βh ∧ βh ≤ cBoundary*ε :=by
  have heHalf:eParent/2 ≤ cBoundary:=by linarith
  have hhHalf:hParent/2 ≤ cBoundary:=by linarith
  constructor
  · rw [heq]; positivity
  constructor
  · rw [heq]; exact mul_le_mul_of_nonneg_right heHalf hε
  constructor
  · rw [heq']; positivity
  · rw [heq']; exact mul_le_mul_of_nonneg_right hhHalf hε
end Oberwolfach
