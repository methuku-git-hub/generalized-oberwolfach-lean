module

public import Oberwolfach.ActualPrescribedOnOldPieces
public import Oberwolfach.ActualOldPieceTargetMatching

@[expose] public section
/-! The old-piece map and anchor map agree everywhere on their common domain
once the run endpoint anchors have their prescribed target values. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_matched_anchor_agreement_from_endpoints
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (hG:G.IsRegularOfDegree 2)
    (H:SimpleGraph V) (u v:actualOldPieceIndex data→V) (q:∀z,H.Walk (u z) (v z)):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(f:{x // x∈A}↪V) (g:{x // x∈data.prescribed}↪V),
    (∀z,(q z).length=(actualOldPieceWalk data z).length)→
    (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
      f ⟨(actualOldPieceWalk data z).getVert k.val,
        Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
        (q z).getVert k.val)→
    (∀r:SelectedRunIndex data.s₂ data.d data.T,∀hp:data.start (.inr r)∈data.prescribed,
      g ⟨data.start (.inr r),hp⟩=u (.inr r))→
    (∀r:SelectedRunIndex data.s₂ data.d data.T,∀hp:data.finish (.inr r)∈data.prescribed,
      g ⟨data.finish (.inr r),hp⟩=v (.inr r))→
    ∀x (ha:x∈A) (hp:x∈data.prescribed),f ⟨x,ha⟩=g ⟨x,hp⟩:=by
  intro A f g hlen hf hs ht
  apply actual_anchor_piece_agreement_from_run_endpoints data hG f g
  · intro r ha hp
    have hh:=hf (.inr r) 0
    have hstart:f ⟨data.start (.inr r),ha⟩=u (.inr r):=by
      simpa only [actualOldPieceWalk,actualOldPieceStart,SimpleGraph.Walk.getVert_zero,Fin.val_zero] using hh
    exact hstart.trans (hs r hp).symm
  · intro r ha hp
    have hh:=hf (.inr r) (Fin.last ((data.path (.inr r)).length))
    have hl:(q (.inr r)).length=(data.path (.inr r)).length:=hlen (.inr r)
    have hqend:(q (.inr r)).getVert ((data.path (.inr r)).length)=v (.inr r):=by
      rw [←hl]
      exact (q (.inr r)).getVert_length
    have hfinish:f ⟨data.finish (.inr r),ha⟩=v (.inr r):=by
      simpa only [actualOldPieceWalk,actualOldPieceFinish,SimpleGraph.Walk.getVert_length,Fin.val_last,hqend] using hh
    exact hfinish.trans (ht r hp).symm
end Oberwolfach
