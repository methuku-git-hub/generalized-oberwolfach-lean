module

public import Oberwolfach.ResidualPathClosingEdge

@[expose] public section
/-! A cycle with at least one deleted edge splits into retained directed
paths, with no deleted vertices and with exact physical-edge coverage. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem cut_cycle_into_retained_paths (H:SimpleGraph V) (R:Finset V)
    (hisol:∀x,x∉R→∀y,¬H.Adj x y) (D:V→V→Prop)
    (a:V) (xs:List V) (hn:(a::xs).Nodup)
    (hchain:List.IsChain D ((a::xs)++[a]))
    (e:Sym2 V) (he:e∈prescribedOrderedPathEdges ((a::xs)++[a]))
    (hmissing:e∉H.edgeFinset):
    ∃ blocks:List (List V),
      blocks.Pairwise (fun p q=>Disjoint p.toFinset q.toFinset) ∧
      (∀ block∈blocks,block.Nodup ∧ List.IsChain H.Adj block ∧ List.IsChain D block) ∧
      (∀x,x∈blocks.flatten ↔ x∈a::xs ∧ x∈R) ∧
      blocks.toFinset.biUnion prescribedOrderedPathEdges =
        (prescribedOrderedPathEdges ((a::xs)++[a])).filter (fun f=>f∈H.edgeFinset) := by
  obtain ⟨v,u,ys,hn',hvertices,hchain',hphys,hdir,hlast,hnot⟩:=
    cycle_rotate_deleted_edge_to_closure H D a xs hn e he hmissing
  let blocks:=retainedPathBlocks H R (v::ys)
  have hbase:=split_path_graph_structure H (v::ys) hn'
  have hfilter:List.Sublist blocks (splitPathByGraph H (v::ys)) := List.filter_sublist
  have hpair:blocks.Pairwise (fun p q=>Disjoint p.toFinset q.toFinset) := hbase.2.2.sublist hfilter
  have hrot:List.IsChain D ((v::ys)++[v]) := hchain'.1 hchain
  have hinfix:(v::ys) <:+: ((v::ys)++[v]) := List.IsPrefix.isInfix (List.prefix_append _ _)
  have hpath:List.IsChain D (v::ys):=hrot.infix hinfix
  have hdirblocks:=split_path_preserves_chain H D (v::ys) hpath
  have hnotE:s(u,v)∉H.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hnot
  refine ⟨blocks,hpair,?_,?_,?_⟩
  · intro block hb
    have hb':block∈splitPathByGraph H (v::ys) := (List.mem_filter.mp hb).1
    exact ⟨(hbase.2.1 block hb').1,(hbase.2.1 block hb').2,hdirblocks block hb'⟩
  · intro x
    rw [retained_path_blocks_cover H R hisol (v::ys) hn' x]
    have hmem:x∈v::ys ↔ x∈a::xs := by
      have hh:=congrArg (fun S:Finset V=>x∈S) hvertices
      simpa only [List.mem_toFinset] using Iff.of_eq hh.symm
    rw [hmem]
  · rw [retained_path_blocks_edges H R hisol (v::ys) hn',split_path_edge_union,hphys]
    have hclose:=ordered_path_append_closing_edge (v::ys) v u hlast
    rw [hclose,Finset.filter_insert]
    simp [hnotE]
end Oberwolfach
