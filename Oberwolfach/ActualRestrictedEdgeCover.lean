module

public import Oberwolfach.ResidualActualPhysicalEdges
public import Oberwolfach.ResidualActualData

@[expose] public section
/-! Cover complement-factor edges by old deleted edges other than the final
paths and by the actual residual graph, using compatible partial maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_restricted_edge_image_cover
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    (F:SimpleGraph X) (hF:F.IsRegularOfDegree 2)
    (a:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed)
    (D:Finset X) (finalEdges:Finset (Sym2 X))
    (fC:{x // x∉D}↪V) (ψ:X→V) (Φ:{x // x∈a.remaining}→V)
    (hold:∀(x:{x // x∉D}),x.val∈a.oldDomain→fC x=ψ x.val)
    (hnew:∀(x:{x // x∉D}) (hx:x.val∈a.remaining),fC x=Φ ⟨x.val,hx⟩):
    (((F.deleteEdges (↑finalEdges:Set (Sym2 X))).induce {x | x∉D}).edgeFinset).image (Sym2.map fC) ⊆
      (a.deletedEdges\finalEdges).image (Sym2.map ψ) ∪
        ((a.graph.induce (↑a.remaining:Set X)).edgeFinset).image (Sym2.map Φ):=by
  classical
  intro edge he
  obtain ⟨e,hmem,rfl⟩:=Finset.mem_image.mp he
  induction e using Sym2.ind with
  | _ x y =>
    have hR:(F.deleteEdges (↑finalEdges:Set (Sym2 X))).Adj x.val y.val:=by
      exact SimpleGraph.mem_edgeFinset.mp hmem
    have hsource:s(x.val,y.val)∈F.edgeFinset\finalEdges:=by
      rw [←SimpleGraph.edgeFinset_deleteEdges]
      exact SimpleGraph.mem_edgeFinset.mpr hR
    by_cases hd:s(x.val,y.val)∈a.deletedEdges
    · have hxo:x.val∈a.oldDomain:=a.deleted_edge_vertices_in_old_domain hCycle _ hd x.val (by simp)
      have hyo:y.val∈a.oldDomain:=a.deleted_edge_vertices_in_old_domain hCycle _ hd y.val (by simp)
      apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨s(x.val,y.val),Finset.mem_sdiff.mpr ⟨hd,(Finset.mem_sdiff.mp hsource).2⟩,?_⟩
      simp only [Sym2.map_mk]
      rw [hold x hxo,hold y hyo]
    · have hgraph:a.graph.Adj x.val y.val:=by
        change s(x.val,y.val)∈a.graph.edgeSet
        apply SimpleGraph.mem_edgeFinset.mp
        rw [SimpleGraph.edgeFinset_deleteEdges]
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hsource).1,hd⟩
      have hnograph:∀z,z∉a.remaining→∀w,¬a.graph.Adj z w:=(a.graph_facts hF).2.2.2.2.1
      have hx:x.val∈a.remaining:=by by_contra h;exact hnograph _ h _ hgraph
      have hy:y.val∈a.remaining:=by by_contra h;exact hnograph _ h _ hgraph.symm
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨s((⟨x.val,hx⟩:{x // x∈a.remaining}),⟨y.val,hy⟩),?_,?_⟩
      · apply SimpleGraph.mem_edgeFinset.mpr
        exact hgraph
      · simp only [Sym2.map_mk]
        rw [hnew x hx,hnew y hy]
end Oberwolfach
