module

public import Oberwolfach.ActualOldPiecePaths
public import Oberwolfach.DisjointActualWalkMatching
public import Oberwolfach.SimpleWalkLengthEmbeddingGetVert

@[expose] public section
/-! The actual old selected runs and component cycles admit one partial
injection matching all of their fixed source positions to target walks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_pieces_match_target_walks
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (H:SimpleGraph V)
    (u v:actualOldPieceIndex data→V)
    (q:∀z,H.Walk (u z) (v z)) (hq:∀z,(q z).IsPath)
    (hlen:∀z,(q z).length=(actualOldPieceWalk data z).length)
    (hqdis:∀z w,z≠w→Disjoint (q z).support.toFinset (q w).support.toFinset):
    ∃φ:{x // x∈Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)}↪V,
      ∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
        φ ⟨(actualOldPieceWalk data z).getVert k.val,
          Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
          (q z).getVert k.val:=by
  classical
  have hsource:=actual_old_piece_walks_are_disjoint_simple_paths data
  obtain ⟨φ,hφ⟩:=disjoint_simple_walk_families_match G H
    (actualOldPieceStart data) (actualOldPieceFinish data)
    (actualOldPieceWalk data) hsource.1 u v q hq hlen hsource.2 hqdis
  refine ⟨φ,?_⟩
  intro z k
  have hh:=hφ z k
  simpa only [simple_walk_length_embedding_getVert] using hh
end Oberwolfach
