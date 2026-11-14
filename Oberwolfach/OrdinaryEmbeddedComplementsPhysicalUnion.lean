module

public import Oberwolfach.OrdinaryCompletedFactorRemainder
public import Oberwolfach.OrdinaryComplementRemainderDecomposition

@[expose] public section
/-! The graph of embedded complementary factors is exactly the union of
their physical edge images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_embedded_complements_physical_union {n q:ℕ}
    (F:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent)
    (f:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n):
    ordinaryEmbeddedComplements F C f = prescribedPhysicalUnion
      (fun u=>(((F u).induce {x | (F u).connectedComponentMk x∉C u}).edgeFinset).image (Sym2.map (f u))) :=by
  let Edges:=fun u=>(((F u).induce {x | (F u).connectedComponentMk x∉C u}).edgeFinset).image (Sym2.map (f u))
  ext v w
  change (ordinaryEmbeddedComplements F C f).Adj v w ↔ (prescribedPhysicalUnion Edges).Adj v w
  constructor
  · intro h
    obtain ⟨u,hu⟩:=SimpleGraph.iSup_adj.mp h
    have hm:s(v,w)∈(((F u).induce {x | (F u).connectedComponentMk x∉C u}).map (f u)).edgeFinset:=
      SimpleGraph.mem_edgeFinset.mpr hu
    rw [SimpleGraph.edgeFinset_map] at hm
    obtain ⟨e,he,heq⟩:=Finset.mem_map.mp hm
    change (SimpleGraph.fromEdgeSet (↑(Finset.univ.biUnion Edges):Set (Sym2 (Fin n)))).Adj v w
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,?_⟩,hu.ne⟩
    exact Finset.mem_image.mpr ⟨e,he,by simpa only [Function.Embedding.sym2Map_apply] using heq⟩
  · intro h
    change (SimpleGraph.fromEdgeSet (↑(Finset.univ.biUnion Edges):Set (Sym2 (Fin n)))).Adj v w at h
    have hm:=(SimpleGraph.fromEdgeSet_adj (↑(Finset.univ.biUnion Edges):Set (Sym2 (Fin n)))).mp h
    obtain ⟨u,_,hu⟩:=Finset.mem_biUnion.mp hm.1
    dsimp [Edges] at hu
    obtain ⟨e,he,heq⟩:=Finset.mem_image.mp hu
    apply SimpleGraph.iSup_adj.mpr
    refine ⟨u,?_⟩
    have hmem:s(v,w)∈(((F u).induce {x | (F u).connectedComponentMk x∉C u}).map (f u)).edgeFinset:=by
      rw [SimpleGraph.edgeFinset_map]
      exact Finset.mem_map.mpr ⟨e,he,by simpa only [Function.Embedding.sym2Map_apply] using heq⟩
    exact SimpleGraph.mem_edgeFinset.mp hmem
end Oberwolfach
