module

public import Oberwolfach.ResidualSplitPathArcs
public import Oberwolfach.ResidualRetainedPathBlocks

@[expose] public section
/-! Removing isolated blocks leaves every retained directed arc. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem retained_path_blocks_arcs (H:SimpleGraph V) (R:Finset V)
    (hisol:∀x,x∉R→∀y,¬H.Adj x y) (xs:List V) (hxs:xs.Nodup):
    (retainedPathBlocks H R xs).toFinset.biUnion prescribedDirectedPathEdges =
      splitPathArcUnion H xs := by
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
      simp [prescribedDirectedPathEdges] at he
    exact Finset.mem_biUnion.mpr ⟨block,List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hb,by simpa using hsub⟩),he⟩
end Oberwolfach
