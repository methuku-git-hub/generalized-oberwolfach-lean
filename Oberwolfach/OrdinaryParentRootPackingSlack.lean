module

public import Oberwolfach.OrdinaryParentDeepCutScaleChoices

@[expose] public section
/-! The selected parent-reference and geometry margins imply the packing
slack required by both initial and later wheel certificates. -/
set_option autoImplicit false
namespace Oberwolfach

theorem ordinary_parent_root_packing_slack
    (h ζparent geomCap ξreserve ζout:ℝ)
    (hζ:ζparent≤h) (hgeom:2*geomCap≤h/2)
    (hξ:ξreserve≤geomCap) (hout:ζout≤geomCap):
    h/2≤(2*h-ζparent)-ξreserve-ζout :=by
  linarith
end Oberwolfach
