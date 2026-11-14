module

public import Oberwolfach.OrdinaryScaledEditFitsInner
public import Oberwolfach.OrdinaryFirstVortexInnerLower

@[expose] public section
/-! The selected global edit and correction rates fit the actual first
vortex level, without assuming a separate local-scale bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_scaled_edits_fit_first_vortex
    {n q D mv:ℕ} {β ε cap ξedit ξAbs:ℝ} (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin q) P D β ε mv) (hcap:0≤cap) (hε:0<ε) (hmv:0<mv)
    (hEdit:ξedit≤cap*ε/1000) (hAbs:ξAbs≤cap*ε/1000):
    ξedit*n+10*ξAbs*n≤cap*(Q.extendedVertices 1).card/4 :=by
  exact ordinary_scaled_edit_fits_inner cap ε ξedit ξAbs n (Q.extendedVertices 1).card hcap hε.le (by positivity)
    (ordinary_first_vortex_inner_lower P Q hε hmv) hEdit hAbs
end Oberwolfach
