module

public import Oberwolfach.OrdinaryTriangleGeometryEarlyInputs
public import Oberwolfach.OrdinaryTriangleInnerNumericSmallerRoot

@[expose] public section
/-! Select the inner tolerances before geometry and allow the geometry to
fix any smaller positive root scale while retaining those tolerances. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_geometry_early_monotone
    (ζ γinner cInitial cLater pmin κe εfactor ηend εrows:ℝ)
    (hζ:0<ζ) (hγ:0<γinner) (hI:0<cInitial) (hL:0<cLater)
    (hp:0<pmin) (hκ:0<κe) (hεf:0<εfactor) (hη:0<ηend) (hrows:0<εrows):
    ∃δ εcount t root eParent hParent γchoice:ℝ,
      0<root ∧
      (∀lam:ℝ,0<lam→lam≤root→
        OrdinaryTriangleInnerNumericParameters pmin κe εfactor ηend εrows δ εcount t lam) ∧
      0<eParent ∧ eParent≤cInitial ∧ eParent≤cLater ∧
      0<hParent ∧ hParent≤cInitial ∧ hParent≤cLater ∧
      0<γchoice ∧ γchoice≤eParent ∧ γchoice≤γinner ∧
      ∀c ε:ℝ,0≤ε→c≤min (ζ*γchoice*(1/4:ℝ)) (ζ*(1/4:ℝ))/2→
        c*ε≤ζ*(γinner/4)*ε:=by
  obtain ⟨δ,εcount,t,root,eParent,hParent,γchoice,hnum,he,heI,heL,hh,hhI,hhL,hγc,hγe,hγi,hmargin⟩:=
    ordinary_triangle_geometry_early_inputs ζ γinner cInitial cLater pmin κe εfactor ηend εrows
      hζ hγ hI hL hp hκ hεf hη hrows
  refine ⟨δ,εcount,t,root,eParent,hParent,γchoice,hnum.lambda_pos,?_,he,heI,heL,hh,hhI,hhL,hγc,hγe,hγi,hmargin⟩
  intro lam hlam hsmall
  exact ordinary_triangle_inner_numeric_smaller_root pmin κe εfactor ηend εrows δ εcount t root lam hp hκ hnum hlam hsmall
end Oberwolfach
