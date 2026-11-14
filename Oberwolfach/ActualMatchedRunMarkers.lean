module

public import Oberwolfach.ActualOldMatchedEmbedding
public import Oberwolfach.ActualSelectedRunMarkers
public import Oberwolfach.ResidualDeletedPathLengths

@[expose] public section
/-! Matching the actual selected runs to their packed wheel runs automatically
preserves all original parent markers on those runs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem matched_actual_run_preserves_parent_markers
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (H:SimpleGraph V)
    (u v:actualOldPieceIndex data→V) (q:∀z,H.Walk (u z) (v z))
    (ψ:X→V):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(f:{x // x∈A}↪V),
    (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩)→
    (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
      f ⟨(actualOldPieceWalk data z).getVert k.val,
        Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
        (q z).getVert k.val)→
    ∀(π:Equiv.Perm V) (root:{i // i∈data.s₂}→V),
    (∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
      (q (.inr r)).getVert (data.c*j)=(π^(r.2.val.1+j)) (root r.1))→
    ∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
      ψ ((data.P r.1.val).getVert (2+data.c*(r.2.val.1+j)))=(π^(r.2.val.1+j)) (root r.1):=by
  classical
  intro A f hψ hf π root hmarks r j hj
  have hlen:(data.path (.inr r)).length=data.c*(r.2.val.2+1-r.2.val.1):=by
    exact (deleted_path_lengths G data.s₁ data.s₂ data.u data.v data.P data.hp data.c data.d
      (lt_of_lt_of_le (by decide : 0<3) data.hc) data.hlen data.T (fun i _=>data.hT i)).2 r.1 r.2
  have hk:data.c*j≤(data.path (.inr r)).length:=by
    rw [hlen]
    exact Nat.mul_le_mul_left data.c hj
  let z:actualOldPieceIndex data:=.inr r
  let k:Fin ((actualOldPieceWalk data z).length+1):=⟨data.c*j,by change data.c*j<(data.path (.inr r)).length+1;omega⟩
  have hx:(actualOldPieceWalk data z).getVert k.val∈A:=
    Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩
  have hh:ψ ((data.path (.inr r)).getVert (data.c*j))=(q (.inr r)).getVert (data.c*j):=by
    change ψ ((actualOldPieceWalk data z).getVert k.val)=(q z).getVert k.val
    rw [hψ _ hx]
    exact hf z k
  rw [←actual_selected_run_marker_getVert data r j hj]
  exact hh.trans (hmarks r j hj)
end Oberwolfach
