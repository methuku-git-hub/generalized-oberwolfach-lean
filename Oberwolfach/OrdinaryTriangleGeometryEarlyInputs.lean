module

public import Oberwolfach.OrdinaryTriangleAsymmetricGeometryMargin
public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy

@[expose] public section
/-! Choose the inner numeric tolerances and the common initial/later
profile margins before the vortex ratio and before the sampled host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_geometry_early_inputs
    (ζ γinner cInitial cLater pmin κe εfactor ηend εrows:ℝ)
    (hζ:0<ζ) (hγ:0<γinner) (hI:0<cInitial) (hL:0<cLater)
    (hp:0<pmin) (hκ:0<κe) (hεf:0<εfactor) (hη:0<ηend) (hrows:0<εrows):
    ∃δ εcount t lam eParent hParent γchoice:ℝ,
      OrdinaryTriangleInnerNumericParameters pmin κe εfactor ηend εrows δ εcount t lam ∧
      0<eParent ∧ eParent≤cInitial ∧ eParent≤cLater ∧
      0<hParent ∧ hParent≤cInitial ∧ hParent≤cLater ∧
      0<γchoice ∧ γchoice≤eParent ∧ γchoice≤γinner ∧
      ∀c ε:ℝ,0≤ε→c≤min (ζ*γchoice*(1/4:ℝ)) (ζ*(1/4:ℝ))/2→
        c*ε≤ζ*(γinner/4)*ε:=by
  obtain ⟨δ,εcount,t,lam,hnum⟩:=ordinary_triangle_inner_numeric_hierarchy pmin κe εfactor ηend εrows
    hp hκ hεf hη hrows
  let eParent:ℝ:=min cInitial cLater/2
  have he:0<eParent:=by dsimp [eParent];positivity
  have heI:eParent≤cInitial:=by
    have hh:=min_le_left cInitial cLater
    dsimp [eParent];linarith
  have heL:eParent≤cLater:=by
    have hh:=min_le_right cInitial cLater
    dsimp [eParent];linarith
  obtain ⟨γchoice,hgc,hge,hgi,hmargin⟩:=ordinary_triangle_asymmetric_geometry_margin ζ γinner eParent hζ hγ he
  exact ⟨δ,εcount,t,lam,eParent,eParent,γchoice,hnum,he,heI,heL,he,heI,heL,hgc,hge,hgi,hmargin⟩
end Oberwolfach
