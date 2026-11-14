module

public import Oberwolfach.EndpointTriangleTransport

@[expose] public section
/-! A vertex-disjoint endpoint-triangle factor on an induced domain lifts to
the original physical graph, preserving its avoided graph and vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem endpoint_triangle_induced_avoiding_factor_lift
    (e:W↪V) (Q F K:SimpleGraph V) (S T Y:Finset V)
    (hS:∀v∈S,∃w,e w=v) (hT:∀v∈T,∃w,e w=v) (hY:Y⊆S∪T)
    (M:Finset (EndpointTriangle (Q.comap e) (F.comap e) (embeddingPullFinset e S) (embeddingPullFinset e T)))
    (hM:∀C∈M,∀D∈M,C≠D→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices D))
    (hcover:M.biUnion endpointTriangleVertices=embeddingPullFinset e Y)
    (havoid:∀C∈M,∀x∈endpointTriangleVertices C,∀y∈endpointTriangleVertices C,¬(K.comap e).Adj x y):
    ∃M':Finset (EndpointTriangle Q F S T),
      (∀C∈M',∀D∈M',C≠D→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices D)) ∧
      M'.biUnion endpointTriangleVertices=Y ∧
      ∀C∈M',∀x∈endpointTriangleVertices C,∀y∈endpointTriangleVertices C,¬K.Adj x y :=by
  have hYrange:∀v∈Y,∃w,e w=v:=by
    intro v hv
    exact (Finset.mem_union.mp (hY hv)).elim (hS v) (hT v)
  let lift:=endpointTriangleLift e Q F S T
  refine ⟨M.image lift,?_,?_,?_⟩
  · intro C hC D hD hne
    obtain ⟨C',hC',rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨D',hD',rfl⟩:=Finset.mem_image.mp hD
    have hne':C'≠D':=fun h=>hne (congrArg lift h)
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    obtain ⟨y,hy,heq⟩:=Finset.mem_image.mp hw
    have hyx:y=x:=e.injective heq
    subst y
    exact Finset.disjoint_left.mp (hM C' hC' D' hD' hne') hx hy
  · have hi:=congrArg (fun A:Finset W=>A.image e) hcover
    rw [embeddingPullFinset_image e Y hYrange] at hi
    apply Eq.trans _ hi
    rw [Finset.biUnion_image,Finset.image_biUnion]
    rfl
  · intro C hC x hx y hy
    obtain ⟨C',hC',rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨x',hx',rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨y',hy',rfl⟩:=Finset.mem_image.mp hy
    exact havoid C' hC' x' hx' y' hy'
end Oberwolfach
