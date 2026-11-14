module

public import Oberwolfach.OrdinaryTriangleFixedInnerActualCover

@[expose] public section
/-! Uniform rate assumptions for the actual-cover certificate follow from
one scaled condition and two scalar budgets at the chosen caps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_capped_rates_inputs
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (p εsup τ ν ηCap ellCap δsample κscale ζfresh βe βh βe₀ βh₀ rate:ℝ)
    (hscaled:OrdinaryTriangleRootFirstScaledConditions Q H X Z p εsup τ ν ηCap
      (p*ellCap+δsample) κscale ζfresh)
    (hE:βe+3*max ηCap ellCap≤βe₀) (hH:βh+2*ellCap≤βh₀)
    (hfinish:ν+ηCap+4*p≤rate):
    ∀ηrate ellrate:ℝ,0≤ηrate→ηrate≤ηCap→0≤ellrate→ellrate≤ellCap→
      βe*Fintype.card (V⊕U)+3*max (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))≤βe₀*Fintype.card (V⊕U) ∧
      βh*Fintype.card (V⊕U)+2*(ellrate*Fintype.card (V⊕U))≤βh₀*Fintype.card (V⊕U) ∧
      OrdinaryTriangleRootFirstScaledConditions Q H X Z p εsup τ ν ηrate (p*ellrate+δsample) κscale ζfresh ∧
      ν+ηrate+4*p≤rate :=by
  intro ηrate ellrate hη hηcap hell hellcap
  have hN:0≤(Fintype.card (V⊕U):ℝ):=by positivity
  have hmax:max (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))≤
      max ηCap ellCap*Fintype.card (V⊕U):=by
    apply max_le
    · exact mul_le_mul_of_nonneg_right (hηcap.trans (le_max_left _ _)) hN
    · exact mul_le_mul_of_nonneg_right (hellcap.trans (le_max_right _ _)) hN
  have hE':=(mul_le_mul_of_nonneg_right hE hN)
  have hH':=(mul_le_mul_of_nonneg_right hH hN)
  have hell':=mul_le_mul_of_nonneg_right hellcap hN
  have hpell:=mul_le_mul_of_nonneg_left hellcap hscaled.hp.le
  refine ⟨?_,?_,?_,by linarith⟩
  · nlinarith only [hmax,hE']
  · nlinarith only [hell',hH']
  · exact ⟨hscaled.hp,hscaled.hp1,hscaled.hτ,hscaled.hκ,hscaled.hζ,hscaled.hε,hscaled.hsupport,
      by linarith [hscaled.hclass],by linarith [hscaled.hblock],hscaled.hpκ,hscaled.hsqrt,hscaled.horder,hscaled.hY,hscaled.hZ⟩
end Oberwolfach
