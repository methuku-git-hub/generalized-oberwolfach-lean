module

public import Oberwolfach.EndpointReplacementPaths

@[expose] public section

/-! Each common replacement path closes to two genuine unordered endpoint
triangles. The roots are used separately and never joined to each other. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem endpoint_path_triangle (Q F : SimpleGraph V) (S T : Finset V) (hST : Disjoint S T)
    (j : Bool) (x y z : V) (hz : z∈({x,y}:Finset V)) (hzclass : z∈if j then T else S)
    (f : Fin 2→V)
    (hf : ClassSparseGreedyGood Q F (endpointPathClass S T j) {x,y} (endpointPathRequirements x y) f) :
    ∃ C : EndpointTriangle Q F S T,endpointTriangleVertices C=insert z (Finset.univ.image f) := by
  obtain ⟨he,hfedge⟩ := endpoint_path_edges Q F S T j x y f hf
  have himage : Finset.univ.image f={f 0,f 1} := by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨i,rfl⟩;fin_cases i <;> simp
    · rintro (rfl|rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  have h0z : f 0≠z := fun h=>(hf.2.1 0).2 (h.symm ▸ hz)
  have h1z : f 1≠z := fun h=>(hf.2.1 1).2 (h.symm ▸ hz)
  have h01 : f 0≠f 1 := fun h=>by have hh:=hf.1 h;norm_num at hh
  have hF0 := hf.2.2.2.1 0 z hz
  have hF1 := hf.2.2.2.1 1 z hz
  have hF01 := hf.2.2.1 0 1
  have hc0 := (hf.2.1 0).1
  have hc1 := (hf.2.1 1).1
  cases j
  · obtain ⟨C,hC⟩ := endpoint_triangle_from_vertices Q F S T hST (f 0) z (f 1)
      (by simpa [endpointPathClass] using hc0) hzclass
      (by simpa [endpointPathClass] using hc1) h1z.symm (he z hz 0).symm hfedge (he z hz 1)
      hF0 hF01 (fun h=>hF1 h.symm)
    refine ⟨C,hC.trans ?_⟩
    rw [himage,Finset.insert_comm]
  · obtain ⟨C,hC⟩ := endpoint_triangle_from_vertices Q F S T hST z (f 0) (f 1) hzclass
      (by simpa [endpointPathClass] using hc0) (by simpa [endpointPathClass] using hc1) h01
      (he z hz 0) (he z hz 1) hfedge (fun h=>hF0 h.symm) (fun h=>hF1 h.symm) hF01
    exact ⟨C,hC.trans (by rw [himage])⟩

end Oberwolfach
