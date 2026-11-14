module

public import Oberwolfach.OrdinaryTriangleRootFirstSampleEvent

@[expose] public section
/-! A smaller preselected matching margin can pay all scaled triangle
conditions while leaving room for the cleanup boundary margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_scaled_conditions_smaller_margin
    (Q:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (p εsup τ ν η ell κ ζ θ:ℝ)
    (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hκ:0<κ) (hζ:0<ζ) (hθ:θ≤ζ*κ)
    (hε:εsup≤p^2/4) (hsupport:τ+ν≤p^2/4)
    (hclass:τ+ν+ell≤θ*p/4) (hblock:ν+η≤θ*p/4)
    (hpκ:p≤4*θ) (hsqrt:20*Real.sqrt (2*p)≤θ/2)
    (horder:2≤θ*p*Fintype.card (V⊕U)/4)
    (hY:∀j:{u:U // u∉B},κ*Fintype.card (V⊕U)≤((ordinaryBoundaryHubSet H B A j).card:ℝ))
    (hZ:∀i:{v:V // v∉A},κ*Fintype.card (V⊕U)≤((ordinaryBoundaryRowSet H A B i).card:ℝ)):
    OrdinaryTriangleRootFirstScaledConditions Q H A B p εsup τ ν η ell κ ζ:=by
  have hθp:θ*p/4≤ζ*κ*p/4:=by
    have hh:=mul_le_mul_of_nonneg_right hθ hp.le
    nlinarith only [hh]
  have hθn:θ*p*Fintype.card (V⊕U)/4≤ζ*κ*p*Fintype.card (V⊕U)/4:=by
    have hh:=mul_le_mul_of_nonneg_right hθp (show (0:ℝ)≤Fintype.card (V⊕U) by positivity)
    nlinarith only [hh]
  refine ⟨hp,hp1,hτ,hκ,hζ,hε,hsupport,hclass.trans hθp,hblock.trans hθp,?_,?_,horder.trans hθn,hY,hZ⟩
  · linarith only [hpκ,hθ]
  · linarith only [hsqrt,hθ]
end Oberwolfach
