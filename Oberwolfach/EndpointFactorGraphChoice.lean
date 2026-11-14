module

public import Oberwolfach.EndpointTriangles
public import Oberwolfach.LocalFactorGraphChoice

@[expose] public section

/-! An endpoint triangle is realized by its actual three-edge graph.
The selected endpoint records are retained while constructing the physical
graph used by simultaneous selection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {Q F:SimpleGraph V} {S T:Finset V}

theorem endpoint_as_local_cycle_exists (hST:Disjoint S T) (C:EndpointTriangle Q F S T):
    ∃ D:LocalOrdinaryCycle Q F (S∪T) 3,localOrdinaryVertices D=endpointTriangleVertices C:=by
  have hc:C.val.card=3:=endpointTriangleVertices_card hST C
  let f:Fin 3≃C.val:=Fintype.equivOfCardEq (by simp only [Fintype.card_fin,Fintype.card_coe,hc])
  let e:Fin 3↪V:=⟨fun i=>(f i).val,fun i j h=>f.injective (Subtype.ext h)⟩
  have hi:Finset.univ.image e=C.val:=by
    ext v
    constructor
    · rintro hv;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv;exact (f i).property
    · intro hv;obtain ⟨i,hi⟩:=f.surjective ⟨v,hv⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,congrArg Subtype.val hi⟩
  obtain ⟨D,hD⟩:=ordinary_cycle_from_embedding Q F (S∪T) (by norm_num : 3≤3) e
    (fun i=>C.property.1 (f i).property)
    (fun i j=>C.property.2.2.2.2 _ (f i).property _ (f j).property)
    (fun i j hij=>C.property.2.2.2.1 _ (f i).property _ (f j).property
      (fun he=>hij.ne (e.injective he)))
  exact ⟨D,hD.trans hi⟩

def endpointAsLocalCycle (hST:Disjoint S T) (C:EndpointTriangle Q F S T):
    LocalOrdinaryCycle Q F (S∪T) 3:=Classical.choose (endpoint_as_local_cycle_exists hST C)

theorem endpointAsLocalCycle_vertices (hST:Disjoint S T) (C:EndpointTriangle Q F S T):
    localOrdinaryVertices (endpointAsLocalCycle hST C)=endpointTriangleVertices C:=
  Classical.choose_spec (endpoint_as_local_cycle_exists hST C)

def endpointFactorGraph (hST:Disjoint S T) (D:Finset (EndpointTriangle Q F S T)):SimpleGraph V:=
  localOrdinaryFactorGraph (D.image (endpointAsLocalCycle hST))

theorem endpointFactorGraph_choice (hST:Disjoint S T) (D:Finset (EndpointTriangle Q F S T))
    (Y:Finset V) (K:SimpleGraph V)
    (hD:∀ C∈D,∀ E∈D,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E))
    (hY:D.biUnion endpointTriangleVertices=Y)
    (hK:∀ C∈D,∀ x∈endpointTriangleVertices C,∀ y∈endpointTriangleVertices C,¬K.Adj x y):
    endpointFactorGraph hST D≤spanningRestriction Q Y ∧
      (∀ v,(endpointFactorGraph hST D).degree v≤2) ∧
      Disjoint (endpointFactorGraph hST D) K:=by
  let M:=D.image (endpointAsLocalCycle hST)
  have hM:∀ C∈M,∀ E∈M,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E):=by
    intro C hC E hE hne
    obtain ⟨C',hC',rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨E',hE',rfl⟩:=Finset.mem_image.mp hE
    rw [endpointAsLocalCycle_vertices,endpointAsLocalCycle_vertices]
    exact hD C' hC' E' hE' (fun he=>hne (congrArg (endpointAsLocalCycle hST) he))
  have hcover:M.biUnion localOrdinaryVertices=Y:=by
    rw [←hY]
    ext v
    simp only [M,Finset.mem_biUnion,Finset.mem_image]
    constructor
    · rintro ⟨_,⟨C,hC,rfl⟩,hv⟩
      exact ⟨C,hC,by simpa only [endpointAsLocalCycle_vertices] using hv⟩
    · rintro ⟨C,hC,hv⟩
      exact ⟨endpointAsLocalCycle hST C,⟨C,hC,rfl⟩,by simpa only [endpointAsLocalCycle_vertices] using hv⟩
  have havoid:∀ C∈M,∀ x∈localOrdinaryVertices C,∀ y∈localOrdinaryVertices C,¬K.Adj x y:=by
    intro C hC
    obtain ⟨C',hC',rfl⟩:=Finset.mem_image.mp hC
    simpa only [endpointAsLocalCycle_vertices] using hK C' hC'
  exact ⟨localOrdinaryFactorGraph_restriction M Y hcover,localOrdinaryFactorGraph_degree M hM,
    localOrdinaryFactorGraph_disjoint M K havoid⟩

end Oberwolfach
