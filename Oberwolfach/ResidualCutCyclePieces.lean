module

public import Oberwolfach.ResidualIntactCycleVertices
public import Oberwolfach.PrescribedOriginalSourcePieces

@[expose] public section
/-! Convert the retained paths of a cut cycle into prescribed-source pieces. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def sourcePieceVerticesUnion (ps:List (PrescribedSourcePiece V)):Finset V :=
  ps.toFinset.biUnion (fun p=>p.vertices.toFinset)

def sourcePieceEdgesUnion (ps:List (PrescribedSourcePiece V)):Finset (Sym2 V) :=
  ps.toFinset.biUnion (fun p=>p.edges)

theorem path_blocks_as_source_pieces (D:V→V→Prop) (blocks:List (List V))
    (hpair:blocks.Pairwise (fun p q=>Disjoint p.toFinset q.toFinset))
    (hblocks:∀ b∈blocks,b.Nodup ∧ List.IsChain D b):
    ∃ ps:List (PrescribedSourcePiece V),
      ps.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀p∈ps,p.OriginalValid D) ∧
      (∀x,x∈sourcePieceVerticesUnion ps ↔ x∈blocks.flatten) ∧
      sourcePieceEdgesUnion ps=blocks.toFinset.biUnion prescribedOrderedPathEdges := by
  let ps:=blocks.map PrescribedSourcePiece.path
  refine ⟨ps,?_,?_,?_,?_⟩
  · rw [List.pairwise_map]
    exact hpair
  · intro p hp
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hp
    exact hblocks b hb
  · intro x
    dsimp [ps]
    simp only [sourcePieceVerticesUnion,Finset.mem_biUnion,List.mem_toFinset,List.mem_map,
      List.mem_flatten,PrescribedSourcePiece.vertices]
    constructor
    · rintro ⟨p,⟨b,hb,rfl⟩,hx⟩
      exact ⟨b,hb,hx⟩
    · rintro ⟨b,hb,hx⟩
      exact ⟨.path b,⟨b,hb,rfl⟩,hx⟩
  · ext e
    dsimp [ps]
    simp only [sourcePieceEdgesUnion,Finset.mem_biUnion,List.mem_toFinset,List.mem_map,
      PrescribedSourcePiece.edges]
    constructor
    · rintro ⟨p,⟨b,hb,rfl⟩,he⟩
      exact ⟨b,hb,he⟩
    · rintro ⟨b,hb,he⟩
      exact ⟨.path b,⟨b,hb,rfl⟩,he⟩
end Oberwolfach
