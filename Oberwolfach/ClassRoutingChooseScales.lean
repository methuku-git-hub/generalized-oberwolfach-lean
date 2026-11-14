module

public import Oberwolfach.ClassRoutingLinearMargins

@[expose] public section
/-! Choose the routing scale and discrepancy tolerance before the order.
Any forbidden degree below the displayed fraction is then affordable. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem class_routing_choose_scales (β:ℝ) (hβ:0<β):
    ∃q c:ℝ,0<q ∧ 0<c ∧
      ∀ζ:ℝ,ζ≤β/16→c/q+2*c+4*q+2*ζ<β:=by
  let q:=min (β/32) 1
  let c:=min (q*β/16) (β/32)
  have hq:0<q:=by dsimp [q]; positivity
  have hc:0<c:=by dsimp [c]; positivity
  refine ⟨q,c,hq,hc,?_⟩
  intro ζ hζ
  have hqhi:q≤β/32:=min_le_left _ _
  have hc1:c≤q*β/16:=min_le_left _ _
  have hc2:c≤β/32:=min_le_right _ _
  have hdiv:c/q≤β/16:=by
    apply (div_le_iff₀ hq).2
    nlinarith
  linarith
end Oberwolfach
