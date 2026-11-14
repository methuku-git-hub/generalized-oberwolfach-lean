module

public import Oberwolfach.OrdinaryTriangleRowBoundary

@[expose] public section
/-! Transport selected endpoint factors to the actual remaining host when
all their physical edges survive, preserving their exact factor graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem endpoint_factor_edge_of_triangle
    (Q F:SimpleGraph V) (S T:Finset V) (hST:Disjoint S T)
    (M:Finset (EndpointTriangle Q F S T)) (C:EndpointTriangle Q F S T) (hC:C∈M)
    (v w:V) (hv:v∈C.val) (hw:w∈C.val) (hne:v≠w):
    (endpointFactorGraph hST M).Adj v w:=by
  rw [endpoint_factor_graph_triangles]
  apply SimpleGraph.iSup_adj.mpr
  refine ⟨⟨C,hC⟩,?_⟩
  exact (spanningRestriction_adj ⊤ C.val v w).mpr ⟨hne,hv,hw⟩

def endpointTriangleToHost
    (Q Q' F:SimpleGraph V) (S T:Finset V) (hST:Disjoint S T)
    (M:Finset (EndpointTriangle Q F S T)) (hsub:endpointFactorGraph hST M≤Q')
    (C:{C:EndpointTriangle Q F S T // C∈M}):EndpointTriangle Q' F S T:=
  ⟨C.val.val,C.val.property.1,C.val.property.2.1,C.val.property.2.2.1,
    (fun v hv w hw hne=>hsub (endpoint_factor_edge_of_triangle Q F S T hST M C.val C.property v w hv hw hne)),
    C.val.property.2.2.2.2⟩

theorem endpoint_factor_transfer_to_host
    (Q Q' F:SimpleGraph V) (S T:Finset V) (hST:Disjoint S T)
    (M:Finset (EndpointTriangle Q F S T)) (hsub:endpointFactorGraph hST M≤Q'):
    ∃M':Finset (EndpointTriangle Q' F S T),
      ((∀C∈M',∀D∈M',C≠D→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices D)) ↔
        (∀C∈M,∀D∈M,C≠D→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices D))) ∧
      M'.biUnion endpointTriangleVertices=M.biUnion endpointTriangleVertices ∧
      endpointFactorGraph hST M'=endpointFactorGraph hST M:=by
  let f:=endpointTriangleToHost Q Q' F S T hST M hsub
  let M':=Finset.univ.image f
  have hf:Function.Injective f:=by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c:EndpointTriangle Q' F S T=>c.val) hab
  have hverts (C:{C:EndpointTriangle Q F S T // C∈M}):endpointTriangleVertices (f C)=endpointTriangleVertices C.val:=rfl
  refine ⟨M',?_,?_,?_⟩
  · constructor
    · intro h C hC D hD hne
      have hh:=h (f ⟨C,hC⟩) (Finset.mem_image.mpr ⟨⟨C,hC⟩,Finset.mem_univ _,rfl⟩)
        (f ⟨D,hD⟩) (Finset.mem_image.mpr ⟨⟨D,hD⟩,Finset.mem_univ _,rfl⟩)
        (by intro he;apply hne;apply Subtype.ext;exact congrArg (fun c:EndpointTriangle Q' F S T=>c.val) he)
      exact hh
    · intro h C hC D hD hne
      obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hC
      obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hD
      exact h a.val a.property b.val b.property (fun he=>hne (congrArg f (Subtype.ext he)))
  · ext v
    simp only [M',Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨a,rfl⟩,hv⟩;exact ⟨a.val,a.property,hv⟩
    · rintro ⟨C,hC,hv⟩;exact ⟨f ⟨C,hC⟩,⟨⟨C,hC⟩,rfl⟩,hv⟩
  · rw [endpoint_factor_graph_triangles,endpoint_factor_graph_triangles]
    ext v w
    simp only [SimpleGraph.iSup_adj,spanningRestriction_adj,SimpleGraph.top_adj]
    constructor
    · rintro ⟨C,hne,hv,hw⟩
      obtain ⟨a,_,ha⟩:=Finset.mem_image.mp C.property
      rw [←ha] at hv hw
      change v∈a.val.val at hv
      change w∈a.val.val at hw
      exact ⟨⟨a.val,a.property⟩,hne,hv,hw⟩
    · rintro ⟨C,hne,hv,hw⟩
      exact ⟨⟨f ⟨C.val,C.property⟩,Finset.mem_image.mpr ⟨⟨C.val,C.property⟩,Finset.mem_univ _,rfl⟩⟩,hne,hv,hw⟩
end Oberwolfach
