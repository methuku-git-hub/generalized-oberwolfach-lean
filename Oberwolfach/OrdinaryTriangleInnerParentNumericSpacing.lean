module

public import Oberwolfach.OrdinaryTriangleDeepInnerExactRows
public import Oberwolfach.OrdinaryTriangleInnerParentSpacingCap

@[expose] public section
/-! Fix the actual row tolerance, deep-parent constants and one vortex
spacing cap together before failure allowances and conflict size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_inner_parent_numeric_spacing
    (α ξ ηHub pmin κe ηend εf Kdom εrows othercap:ℝ)
    (hα:0<α) (hξ:0≤ξ) (hgap:ξ<ηHub) (hp:0<pmin) (hκ:0<κe)
    (hη:0<ηend) (hεf:0<εf) (hK:0<Kdom) (hrows:0<εrows)
    (hrowsGeom:εrows≤min (pmin^4/16) (pmin^3/2)) (hother:0<othercap):
    ∃γold κold δ t lam bold Bold βcap:ℝ,
      OrdinaryDeepNumericParameters pmin κe (1/Kdom) ηend εf (2*Kdom)
        γold κold δ εrows t lam bold Bold ∧
      OrdinaryTriangleInnerNumericParameters pmin κe εf ηend εrows δ εrows t lam ∧
      0<βcap ∧ βcap≤othercap ∧ ∀β:ℝ,0≤β→β≤βcap→
        β≤1/4 ∧ β≤α/8 ∧ ξ+2*β<ηHub ∧ β≤2*δ*κe*pmin :=by
  obtain ⟨γold,κold,δ,t,lam,bold,Bold,hdeep,hinner⟩:=
    ordinary_triangle_deep_inner_exact_rows_hierarchy pmin κe (1/Kdom) ηend εf (2*Kdom) εrows
      hp hκ (by positivity) hη hεf (by positivity) hrows hrowsGeom
  obtain ⟨βcap,hβcap,hβother,hspacing⟩:=ordinary_triangle_inner_parent_spacing_cap α ξ ηHub δ κe pmin othercap
    hα hξ hgap hdeep.delta_pos hκ hp hother
  exact ⟨γold,κold,δ,t,lam,bold,Bold,βcap,hdeep,hinner,hβcap,hβother,hspacing⟩
end Oberwolfach
