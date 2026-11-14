module

public import Oberwolfach.ResidualCutCyclePieces

@[expose] public section
/-! Represent a retained part of an ordered source cycle by directed source
pieces: the cycle itself if intact, and directed paths if cut. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem retained_cycle_source_pieces (H:SimpleGraph V) (R:Finset V)
    (hisol:∀x,x∉R→∀y,¬H.Adj x y) (D:V→V→Prop)
    (a:V) (xs:List V) (hn:(a::xs).Nodup) (hlen:3≤(a::xs).length)
    (hchain:List.IsChain D ((a::xs)++[a])):
    ∃ ps:List (PrescribedSourcePiece V),
      ps.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀p∈ps,p.OriginalValid D) ∧
      (∀x,x∈sourcePieceVerticesUnion ps ↔ x∈a::xs ∧ x∈R) ∧
      sourcePieceEdgesUnion ps=(prescribedOrderedPathEdges ((a::xs)++[a])).filter (fun e=>e∈H.edgeFinset) := by
  by_cases hkeep:∀e∈prescribedOrderedPathEdges ((a::xs)++[a]),e∈H.edgeFinset
  · have hsurv: (a::xs).toFinset⊆R := intact_cycle_vertices_survive H R hisol a xs (by omega) hkeep
    refine ⟨[.cycle a xs],by simp,?_,?_,?_⟩
    · intro p hp
      have hp':p=.cycle a xs := by simpa using hp
      subst p
      exact ⟨hn,hlen,hchain⟩
    · intro x
      have heq:x∈sourcePieceVerticesUnion [.cycle a xs] ↔ x∈a::xs := by
        simp [sourcePieceVerticesUnion,PrescribedSourcePiece.vertices]
      rw [heq]
      constructor
      · intro hx
        exact ⟨hx,hsurv (List.mem_toFinset.mpr hx)⟩
      · exact And.left
    · have heq:sourcePieceEdgesUnion [.cycle a xs]=prescribedOrderedPathEdges ((a::xs)++[a]) := by
        simp [sourcePieceEdgesUnion,PrescribedSourcePiece.edges]
      rw [heq]
      exact (Finset.filter_true_of_mem hkeep).symm
  · push_neg at hkeep
    obtain ⟨e,he,hmissing⟩:=hkeep
    obtain ⟨blocks,hpair,hblocks,hvertices,hedges⟩:=cut_cycle_into_retained_paths H R hisol D a xs hn hchain e he hmissing
    obtain ⟨ps,hp,hvalid,hpsverts,hpsedges⟩:=path_blocks_as_source_pieces D blocks hpair
      (by intro block hb;exact ⟨(hblocks block hb).1,(hblocks block hb).2.2⟩)
    refine ⟨ps,hp,hvalid,?_,?_⟩
    · intro x
      exact (hpsverts x).trans (hvertices x)
    · exact hpsedges.trans hedges
end Oberwolfach
