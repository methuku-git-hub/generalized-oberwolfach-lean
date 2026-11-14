module

public import Oberwolfach.FirstVortexGlobalGeometryEventually

@[expose] public section
/-! A diagnostic for the remaining order of the global load and balance
scales. These are consequences of the displayed scalar bounds, not a
statement about the truth of the main theorem. -/
set_option autoImplicit false
namespace Oberwolfach

theorem first_vortex_global_geometry_order_diagnostic
    (epsilon epsilonInner deltaSmall zetaChange x:ℝ)
    (hInner:epsilon/2≤epsilonInner)
    (hGlobal:epsilonInner<deltaSmall/4)
    (hChange:4*deltaSmall≤zetaChange) (hCap:zetaChange≤x):
    8*epsilon<x :=by
  linarith
end Oberwolfach
