module

public import Oberwolfach.OrdinaryTriangleInnerClassMargins
public import Oberwolfach.OrdinaryTriangleRootFirstSampleEvent

@[expose] public section
/-! Turn an inner-scale class lower bound into the ambient-scaled finish
conditions, with a matching capacity linear in the vortex scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_inner_scaled_conditions
    (Q:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (γ εv p εsup τ ν η ell ζ:ℝ)
    (hγ:0<γ) (hεv:0<εv) (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hζ:0<ζ)
    (hsize:(εv/4)*Fintype.card (V⊕U)≤(A.card:ℝ))
    (hY:∀j:{u:U // u∉B},γ*A.card≤((ordinaryBoundaryHubSet H B A j).card:ℝ))
    (hZ:∀i:{v:V // v∉A},γ*A.card≤((ordinaryBoundaryRowSet H A B i).card:ℝ))
    (hε:εsup≤p^2/4) (hsupport:τ+ν≤p^2/4)
    (hclass:τ+ν+ell≤(ζ*(γ/4)*εv)*p/4)
    (hblock:ν+η≤(ζ*(γ/4)*εv)*p/4)
    (hpκ:p≤4*(ζ*(γ/4)*εv)) (hsqrt:20*Real.sqrt (2*p)≤(ζ*(γ/4)*εv)/2)
    (horder:2≤(ζ*(γ/4)*εv)*p*Fintype.card (V⊕U)/4):
    OrdinaryTriangleRootFirstScaledConditions Q H A B p εsup τ ν η ell ((γ/4)*εv) ζ:=by
  have hk:0<(γ/4)*εv:=by positivity
  have hscale:((γ/4)*εv)*Fintype.card (V⊕U)≤γ*A.card:=by
    have hh:=mul_le_mul_of_nonneg_left hsize hγ.le
    nlinarith only [hh]
  refine ⟨hp,hp1,hτ,hk,hζ,hε,hsupport,?_,?_,?_,?_,?_,?_,?_⟩
  · convert hclass using 1 <;> ring
  · convert hblock using 1 <;> ring
  · convert hpκ using 1 <;> ring
  · convert hsqrt using 1 <;> ring
  · convert horder using 1 <;> ring
  · exact fun j=>hscale.trans (hY j)
  · exact fun i=>hscale.trans (hZ i)
end Oberwolfach
