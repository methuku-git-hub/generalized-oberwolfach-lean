module

public import Oberwolfach.OrdinaryAsymmetricGeometryParentMarginFixedLateRateAndCap

@[expose] public section
/-! The geometry selector's boundary-aware matching coefficient can be
chosen below the fixed inner triangle factor margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_asymmetric_geometry_margin
    (ζ γinner eParent:ℝ) (hζ:0<ζ) (hγ:0<γinner) (he:0<eParent):
    ∃γchoice:ℝ,0<γchoice ∧ γchoice≤eParent ∧ γchoice≤γinner ∧
    ∀c ε:ℝ,0≤ε→c≤min (ζ*γchoice*(1/4:ℝ)) (ζ*(1/4:ℝ))/2→
      c*ε≤ζ*(γinner/4)*ε:=by
  let γchoice:=min γinner eParent/2
  have hgc:0<γchoice:=by dsimp [γchoice];positivity
  have hge:γchoice≤eParent:=by
    have hh:=min_le_right γinner eParent
    dsimp [γchoice];linarith
  have hgi:γchoice≤γinner:=by
    have hh:=min_le_left γinner eParent
    dsimp [γchoice];linarith
  refine ⟨γchoice,hgc,hge,hgi,?_⟩
  intro c ε hε hc
  have hcap:0≤ζ*γchoice*(1/4:ℝ):=by positivity
  have hleft:=min_le_left (ζ*γchoice*(1/4:ℝ)) (ζ*(1/4:ℝ))
  have hc1:c≤ζ*γchoice*(1/4:ℝ):=by linarith
  have hcoef:ζ*γchoice*(1/4:ℝ)≤ζ*(γinner/4):=by
    have hh:=mul_le_mul_of_nonneg_left hgi hζ.le
    nlinarith only [hh]
  exact mul_le_mul_of_nonneg_right (hc1.trans hcoef) hε
end Oberwolfach
