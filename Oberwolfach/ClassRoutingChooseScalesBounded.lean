module

public import Oberwolfach.ClassRoutingLinearMargins

@[expose] public section
/-! Choose routing and discrepancy scales small enough both to permit the
path corrections and to fit a previously fixed deletion budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem class_routing_choose_scales_bounded (β δ:ℝ) (hβ:0<β) (hδ:0<δ):
    ∃q c:ℝ,0<q ∧ 0<c ∧ q≤δ/16 ∧ c≤δ/16 ∧
      ∀ζ:ℝ,ζ≤β/16→c/q+2*c+4*q+2*ζ<β:=by
  let q:=min (β/32) (δ/16)
  let c:=min (q*β/16) (min (β/32) (δ/16))
  have hq:0<q:=by dsimp [q]; positivity
  have hc:0<c:=by dsimp [c]; positivity
  have hqδ:q≤δ/16:=min_le_right _ _
  have hcδ:c≤δ/16:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨q,c,hq,hc,hqδ,hcδ,?_⟩
  intro ζ hζ
  have hqhi:q≤β/32:=min_le_left _ _
  have hc1:c≤q*β/16:=min_le_left _ _
  have hc2:c≤β/32:=(min_le_right _ _).trans (min_le_left _ _)
  have hdiv:c/q≤β/16:=by
    apply (div_le_iff₀ hq).2
    nlinarith
  linarith
end Oberwolfach
