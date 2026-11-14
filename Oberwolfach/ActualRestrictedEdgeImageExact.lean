module

public import Oberwolfach.ActualRestrictedEdgeCover

@[expose] public section
/-! When the old nonfinal edges and the remaining graph avoid deleted path
interiors, the old and new edge images are exactly the complement embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_restricted_edge_image_exact
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    (F:SimpleGraph X) (hF:F.IsRegularOfDegree 2) (a:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed)
    (D:Finset X) (finalEdges:Finset (Sym2 X))
    (fC:{x // x∉D}↪V) (ψ:X→V) (Φ:{x // x∈a.remaining}→V)
    (hold:∀(x:{x // x∉D}),x.val∈a.oldDomain→fC x=ψ x.val)
    (hnew:∀(x:{x // x∉D}) (hx:x.val∈a.remaining),fC x=Φ ⟨x.val,hx⟩)
    (hOldOutside:∀e∈a.deletedEdges\finalEdges,∀x∈e.toFinset,x∉D)
    (hRemOutside:∀x∈a.remaining,x∉D) (hFinalDeleted:finalEdges⊆a.deletedEdges):
    (((F.deleteEdges (↑finalEdges:Set (Sym2 X))).induce {x | x∉D}).edgeFinset).image (Sym2.map fC)=
      (a.deletedEdges\finalEdges).image (Sym2.map ψ) ∪
        ((a.graph.induce (↑a.remaining:Set X)).edgeFinset).image (Sym2.map Φ):=by
  apply Finset.Subset.antisymm
  · exact actual_restricted_edge_image_cover F hF a hCycle D finalEdges fC ψ Φ hold hnew
  · intro e he
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨s,hs,rfl⟩:=Finset.mem_image.mp he
      induction s using Sym2.ind with
      | _ x y =>
        have hx:x∉D:=hOldOutside s(x,y) hs x (by simp)
        have hy:y∉D:=hOldOutside s(x,y) hs y (by simp)
        have hdx:x∈a.oldDomain:=a.deleted_edge_vertices_in_old_domain hCycle _ (Finset.mem_sdiff.mp hs).1 x (by simp)
        have hdy:y∈a.oldDomain:=a.deleted_edge_vertices_in_old_domain hCycle _ (Finset.mem_sdiff.mp hs).1 y (by simp)
        let x':{x // x∉D}:=⟨x,hx⟩
        let y':{y // y∉D}:=⟨y,hy⟩
        have hmem:s(x',y')∈((F.deleteEdges (↑finalEdges:Set (Sym2 X))).induce {x | x∉D}).edgeFinset:=by
          apply SimpleGraph.mem_edgeFinset.mpr
          change (F.deleteEdges (↑finalEdges:Set (Sym2 X))).Adj x y
          have he':s(x,y)∈(F.deleteEdges (↑finalEdges:Set (Sym2 X))).edgeFinset:=by
            rw [SimpleGraph.edgeFinset_deleteEdges]
            exact Finset.mem_sdiff.mpr ⟨a.deleted_edges_subset_factor (Finset.mem_sdiff.mp hs).1,(Finset.mem_sdiff.mp hs).2⟩
          exact SimpleGraph.mem_edgeFinset.mp he' 
        refine Finset.mem_image.mpr ⟨s(x',y'),hmem,?_⟩
        simp only [Sym2.map_mk]
        rw [hold x' hdx,hold y' hdy]
    · obtain ⟨s,hs,rfl⟩:=Finset.mem_image.mp he
      induction s using Sym2.ind with
      | _ x y =>
        have hg:a.graph.Adj x.val y.val:=SimpleGraph.mem_edgeFinset.mp hs
        have hf:F.Adj x.val y.val:=(a.graph_facts hF).1 hg
        have hnot:s(x.val,y.val)∉a.deletedEdges:=by
          have hm:s(x.val,y.val)∈a.graph.edgeFinset:=SimpleGraph.mem_edgeFinset.mpr hg
          rw [SimpleGraph.edgeFinset_deleteEdges] at hm
          exact (Finset.mem_sdiff.mp hm).2
        let x':{x // x∉D}:=⟨x.val,hRemOutside x.val x.property⟩
        let y':{y // y∉D}:=⟨y.val,hRemOutside y.val y.property⟩
        have hmem:s(x',y')∈((F.deleteEdges (↑finalEdges:Set (Sym2 X))).induce {x | x∉D}).edgeFinset:=by
          apply SimpleGraph.mem_edgeFinset.mpr
          change (F.deleteEdges (↑finalEdges:Set (Sym2 X))).Adj x.val y.val
          have he':s(x.val,y.val)∈(F.deleteEdges (↑finalEdges:Set (Sym2 X))).edgeFinset:=by
            rw [SimpleGraph.edgeFinset_deleteEdges]
            exact Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hf,fun he=>hnot (hFinalDeleted he)⟩
          exact SimpleGraph.mem_edgeFinset.mp he' 
        refine Finset.mem_image.mpr ⟨s(x',y'),hmem,?_⟩
        simp only [Sym2.map_mk]
        rw [hnew x' x.property,hnew y' y.property]
end Oberwolfach
