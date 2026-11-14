module

public import Oberwolfach.GraphFourPieceInnerSubset
public import Oberwolfach.LongThreeGraphDegree

@[expose] public section
/-! Degree bound following the four-piece inner containment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W:Type} [Fintype W] [DecidableEq W]

theorem graph_four_piece_inner_degree_small (G A B C D:SimpleGraph W) (Ω:Finset W) (ν η limit:ℝ)
    (hAsub:A≤G) (hA:Disjoint A (spanningRestriction G Ω))
    (hB:∀w,(B.degree w:ℝ)≤ν)
    (hC:∀w,((spanningRestriction C Ω).degree w:ℝ)≤η)
    (hD:∀w,((spanningRestriction D Ω).degree w:ℝ)≤limit):
    ∀w,((spanningRestriction (((A⊔B)⊔C)⊔D) Ω).degree w:ℝ)≤ν+η+limit:=by
  intro w
  have hs:=graph_four_piece_inner_subset G A B C D Ω hAsub hA
  have hd₁:=SimpleGraph.degree_le_of_le hs (v:=w)
  have hd₂:=long_three_graph_degree_bound B (spanningRestriction C Ω) (spanningRestriction D Ω) w
  have hn:=hd₁.trans hd₂
  have hr:((spanningRestriction (((A⊔B)⊔C)⊔D) Ω).degree w:ℝ)≤
      (B.degree w:ℝ)+((spanningRestriction C Ω).degree w:ℝ)+((spanningRestriction D Ω).degree w:ℝ):=by
    exact_mod_cast hn
  exact hr.trans (add_le_add (add_le_add (hB w) (hC w)) (hD w))
end Oberwolfach
