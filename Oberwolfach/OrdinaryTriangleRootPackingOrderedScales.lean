module

public import Oberwolfach.OrdinaryTrianglePackingSelectedError
public import Oberwolfach.OrdinaryTriangleParentRootScaleForPacking

@[expose] public section
/-! The packing theorem fixes its error first; the triangle sampling and
parent-reference errors are then selected below that same error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_packing_ordered_scales
    (α:ℝ) (hα:0<α) (k:ℕ) (hk:4≤k) (hkN:ordinaryTrianglePackingThreshold α hα≤k)
    (βH c B ω pstar δ h ηcap ζcap:ℝ)
    (hβH:0<βH) (hc:0<c) (hB:0<B) (hω:0<ω) (hp:0<pstar)
    (hδ:0<δ) (hδ1:δ<1/4) (hh:0<h) (hηcap:0<ηcap) (hcap:0<ζcap) (hcapH:ζcap≤h):
    let εstar:=ordinaryTrianglePackingError α hα k hkN βH c B ω pstar δ h hβH hc hB hω hp hδ hδ1 hh;
    ∃ηH ζ rate lam:ℝ,0<ηH ∧ ηH≤ηcap ∧ 2*ηH<εstar ∧ 0<ζ ∧ 0<rate ∧ 0<lam ∧ ζ≤ζcap ∧
    ∃N₀:ℕ,1≤N₀ ∧
    OrdinaryTriangleEditScaleAt βH ηH B ω pstar (βH/2) (2*ηH) ζ rate N₀ ∧
    OrdinaryUniformRootReferenceAtScale 3 (by omega) k α (βH/2) c (B/(ω*pstar^(2*3-1)))
      (2*h-ζ) δ (2*ηH) ω ((εstar-2*ηH)/2) lam :=by
  intro εstar
  have hεstar:0<εstar:=ordinary_triangle_packing_selected_error_pos α hα k hkN βH c B ω pstar δ h
    hβH hc hB hω hp hδ hδ1 hh
  exact ordinary_triangle_parent_root_scale_for_packing k hk α βH c B ω pstar δ h εstar ηcap ζcap
    hβH hc.le hB.le hω hp hδ (by linarith) hh hεstar hηcap hcap hcapH
end Oberwolfach
