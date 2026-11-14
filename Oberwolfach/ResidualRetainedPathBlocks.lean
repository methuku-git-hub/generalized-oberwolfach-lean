module

public import Oberwolfach.ResidualChainIsolated

@[expose] public section
/-! Remove exactly the isolated blocks outside the surviving vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def retainedPathBlocks (H:SimpleGraph V) (R:Finset V) (xs:List V):List (List V) :=
  (splitPathByGraph H xs).filter (fun block=>block.toFinset⊆R)

theorem removed_split_block_singleton (H:SimpleGraph V) (R:Finset V)
    (hisol:∀x,x∉R→∀y,¬H.Adj x y) (xs block:List V) (hxs:xs.Nodup)
    (hb:block∈splitPathByGraph H xs) (hnot:¬block.toFinset⊆R):
    ∃x,x∉R ∧ block=[x] := by
  have hex:∃x,x∈block.toFinset ∧ x∉R := by
    by_contra h
    apply hnot
    intro x hx
    by_contra hn
    exact h ⟨x,hx,hn⟩
  obtain ⟨x,hx,hxR⟩:=hex
  have hc:=((split_path_graph_structure H xs hxs).2.1 block hb).2
  exact ⟨x,hxR,chain_with_isolated_vertex_singleton H block hc x (List.mem_toFinset.mp hx) (hisol x hxR)⟩

theorem retained_path_blocks_cover (H:SimpleGraph V) (R:Finset V)
    (hisol:∀x,x∉R→∀y,¬H.Adj x y) (xs:List V) (hxs:xs.Nodup) (x:V):
    x∈(retainedPathBlocks H R xs).flatten ↔ x∈xs ∧ x∈R := by
  constructor
  · intro hx
    obtain ⟨block,hblock,hx⟩:=List.mem_flatten.mp hx
    have hh:=List.mem_filter.mp hblock
    have hxs':x∈(splitPathByGraph H xs).flatten := List.mem_flatten.mpr ⟨block,hh.1,hx⟩
    have hflat:=split_ordered_path_flatten (fun x y=>decide (H.Adj x y)) xs
    refine ⟨?_,(of_decide_eq_true hh.2) (List.mem_toFinset.mpr hx)⟩
    simpa [splitPathByGraph,hflat] using hxs'
  · rintro ⟨hx,hxR⟩
    have hflat:=split_ordered_path_flatten (fun x y=>decide (H.Adj x y)) xs
    have hx':x∈(splitPathByGraph H xs).flatten := by simpa [splitPathByGraph,hflat] using hx
    obtain ⟨block,hblock,hxblock⟩:=List.mem_flatten.mp hx'
    have hsub:block.toFinset⊆R := by
      by_contra hn
      obtain ⟨y,hyR,hblockeq⟩:=removed_split_block_singleton H R hisol xs block hxs hblock hn
      rw [hblockeq] at hxblock
      have hxy:x=y:=by simpa using hxblock
      subst x
      exact hyR hxR
    exact List.mem_flatten.mpr ⟨block,List.mem_filter.mpr ⟨hblock,by simpa using hsub⟩,hxblock⟩

theorem retained_path_blocks_edges (H:SimpleGraph V) (R:Finset V)
    (hisol:∀x,x∉R→∀y,¬H.Adj x y) (xs:List V) (hxs:xs.Nodup):
    (retainedPathBlocks H R xs).toFinset.biUnion prescribedOrderedPathEdges =
      splitPathEdgeUnion H xs := by
  ext e
  constructor
  · intro he
    obtain ⟨block,hblock,he⟩:=Finset.mem_biUnion.mp he
    have hb: block∈splitPathByGraph H xs := (List.mem_filter.mp (List.mem_toFinset.mp hblock)).1
    exact Finset.mem_biUnion.mpr ⟨block,List.mem_toFinset.mpr hb,he⟩
  · intro he
    obtain ⟨block,hblock,he⟩:=Finset.mem_biUnion.mp he
    have hb: block∈splitPathByGraph H xs := List.mem_toFinset.mp hblock
    have hsub:block.toFinset⊆R := by
      by_contra hn
      obtain ⟨x,_,hblockeq⟩:=removed_split_block_singleton H R hisol xs block hxs hb hn
      subst block
      simp [prescribedOrderedPathEdges] at he
    exact Finset.mem_biUnion.mpr ⟨block,List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hb,by simpa using hsub⟩),he⟩
end Oberwolfach
