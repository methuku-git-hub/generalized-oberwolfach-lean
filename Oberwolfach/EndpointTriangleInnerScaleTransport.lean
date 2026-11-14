module

public import Oberwolfach.EndpointTriangleTransport
public import Oberwolfach.EndpointWeightScaleTransfer

@[expose] public section
/-! Transfer endpoint-triangle weights to a smaller induced physical domain
without normalizing them by the unused ambient vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem endpoint_triangle_inner_scale_transport
    (e:W↪V) (Q F:SimpleGraph V) (S T:Finset V)
    (hS:∀v∈S,∃w,e w=v) (hT:∀v∈T,∃w,e w=v)
    (a b B K η:ℝ) (ha:0<a) (han:a≤Fintype.card W) (hK:0≤K)
    (hsize:(Fintype.card W:ℝ)≤K*a) (hb:0≤b) (hB:0≤B)
    (wt:EndpointTriangle Q F S T→ℝ)
    (hw:∀C,b/a^2≤wt C ∧ wt C≤B/a^2)
    (hload:∀v∈S∪T,|1-hypergraphWeightedDegree endpointTriangleVertices wt v|≤η):
    ∃wi:EndpointTriangle (Q.comap e) (F.comap e) (embeddingPullFinset e S) (embeddingPullFinset e T)→ℝ,
      (∀C,b/(Fintype.card W:ℝ)^2≤wi C ∧ wi C≤(B*K^2)/(Fintype.card W:ℝ)^2) ∧
      (∀v∈embeddingPullFinset e S∪embeddingPullFinset e T,
        |1-hypergraphWeightedDegree endpointTriangleVertices wi v|≤η) :=by
  let wi:=fun C=>wt (endpointTriangleLift e Q F S T C)
  refine ⟨wi,?_,?_⟩
  · intro C
    exact endpoint_weight_scale_transfer a (Fintype.card W) b B K (wi C) ha han hK hsize hb hB
      (hw _).1 (hw _).2
  · intro v hv
    have hv':e v∈S∪T:=by simpa only [Finset.mem_union,embeddingPullFinset_mem] using hv
    have hh:=endpointTriangleLift_weighted_degree e Q F S T hS hT wt v
    rw [hh]
    exact hload (e v) hv'
end Oberwolfach
