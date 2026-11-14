module

public import Oberwolfach.ResidualSplitPathEdges
public import Oberwolfach.FactorDirectedEdgesToPhysical
public import Oberwolfach.PrescribedPathDirectedEdges

@[expose] public section
/-! The split blocks are disjoint ordered paths in the retained graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem split_path_graph_structure (H:SimpleGraph V) (xs:List V) (hxs:xs.Nodup):
    (splitPathByGraph H xs).flatten=xs ∧
    (∀ block∈splitPathByGraph H xs,block.Nodup ∧ List.IsChain H.Adj block) ∧
    (splitPathByGraph H xs).Pairwise (fun p q=>Disjoint p.toFinset q.toFinset) := by
  have hflat:(splitPathByGraph H xs).flatten=xs := split_ordered_path_flatten _ xs
  have hn:(splitPathByGraph H xs).flatten.Nodup := by rw [hflat];exact hxs
  obtain ⟨hblocks,hpair⟩:=List.nodup_flatten.mp hn
  refine ⟨hflat,?_,?_⟩
  · intro block hblock
    refine ⟨hblocks block hblock,?_⟩
    apply (prescribed_directed_edges_chain H.Adj block).2
    intro e he
    rcases e with ⟨x,y⟩
    have hp:s(x,y)∈prescribedOrderedPathEdges block := directed_path_edge_is_physical block x y he
    have hu:s(x,y)∈splitPathEdgeUnion H xs := by
      exact Finset.mem_biUnion.mpr ⟨block,List.mem_toFinset.mpr hblock,hp⟩
    rw [split_path_edge_union] at hu
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using (Finset.mem_filter.mp hu).2
  · apply hpair.imp
    intro p q hd
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact List.disjoint_left.mp hd (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy)
end Oberwolfach
