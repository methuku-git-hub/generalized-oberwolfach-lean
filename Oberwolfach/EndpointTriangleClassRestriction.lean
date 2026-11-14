module

public import Oberwolfach.EndpointFactorHostTransfer

@[expose] public section
/-! A triangle using only the surviving two endpoint classes remains an
endpoint triangle on those actual classes, with the same physical vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def endpointTriangleToClasses (Q F:SimpleGraph V) (S T S' T':Finset V)
    (hST:Disjoint S T) (hS:S'⊆S) (hT:T'⊆T)
    (C:EndpointTriangle Q F S T) (hC:C.val⊆S'∪T'):EndpointTriangle Q F S' T':=by
  have heS:C.val∩S=C.val∩S':=by
    ext v
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hv,hvS⟩
      rcases Finset.mem_union.mp (hC hv) with hvS'|hvT'
      · exact ⟨hv,hvS'⟩
      · exact (Finset.disjoint_left.mp hST hvS (hT hvT')).elim
    · rintro ⟨hv,hvS'⟩;exact ⟨hv,hS hvS'⟩
  have heT:C.val∩T=C.val∩T':=by
    ext v
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hv,hvT⟩
      rcases Finset.mem_union.mp (hC hv) with hvS'|hvT'
      · exact (Finset.disjoint_left.mp hST (hS hvS') hvT).elim
      · exact ⟨hv,hvT'⟩
    · rintro ⟨hv,hvT'⟩;exact ⟨hv,hT hvT'⟩
  refine ⟨C.val,hC,?_,?_,C.property.2.2.2.1,C.property.2.2.2.2⟩
  · rw [←heS];exact C.property.2.1
  · rw [←heT];exact C.property.2.2.1

theorem endpoint_factor_restrict_classes
    (Q F:SimpleGraph V) (S T S' T':Finset V) (hST:Disjoint S T) (hST':Disjoint S' T')
    (hS:S'⊆S) (hT:T'⊆T) (M:Finset (EndpointTriangle Q F S T))
    (hcover:M.biUnion endpointTriangleVertices⊆S'∪T'):
    ∃M':Finset (EndpointTriangle Q F S' T'),
      ((∀C∈M',∀D∈M',C≠D→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices D)) ↔
        (∀C∈M,∀D∈M,C≠D→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices D))) ∧
      M'.biUnion endpointTriangleVertices=M.biUnion endpointTriangleVertices ∧
      endpointFactorGraph hST' M'=endpointFactorGraph hST M:=by
  have hC (C:{C:EndpointTriangle Q F S T // C∈M}):C.val.val⊆S'∪T':=by
    intro v hv
    exact hcover (Finset.mem_biUnion.mpr ⟨C.val,C.property,hv⟩)
  let f:=fun C:{C:EndpointTriangle Q F S T // C∈M}=>endpointTriangleToClasses Q F S T S' T' hST hS hT C.val (hC C)
  let M':=Finset.univ.image f
  refine ⟨M',?_,?_,?_⟩
  · constructor
    · intro h C hC D hD hne
      have hh:=h (f ⟨C,hC⟩) (Finset.mem_image.mpr ⟨⟨C,hC⟩,Finset.mem_univ _,rfl⟩)
        (f ⟨D,hD⟩) (Finset.mem_image.mpr ⟨⟨D,hD⟩,Finset.mem_univ _,rfl⟩)
        (by intro he;apply hne;apply Subtype.ext;exact congrArg (fun c:EndpointTriangle Q F S' T'=>c.val) he)
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
