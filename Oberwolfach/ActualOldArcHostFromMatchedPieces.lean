module

public import Oberwolfach.ActualMatchedPieceDirectedArcs
public import Oberwolfach.ActualOldArcsFromReindexedBufferedData

@[expose] public section
/-! Transfer the matched piece directions to every old source arc after
removing the reindexed final paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_arc_host_from_matched_pieces
    {X V K J I:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J] [Fintype I]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (pieces:List (PrescribedSourcePiece X)) (D:X→X→Prop)
    (hpair:pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀p∈pieces,p.OriginalValid D)
    (hArcs:∀x y,D x y↔(x,y)∈sourcePieceArcsUnion pieces)
    (halign:∀x,D x (factorCycleOrientation G e x))
    (data:ActualResidualData (K:=K) (J:=J) G) (ψ:X→V) (H:Finset (V×V))
    (b:I≃{i // i∈data.s₁}) (ext:∀i:I,Fin (data.c*data.d+5)↪X)
    (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hsupp:∀i,(data.P (b i).val).support=List.ofFn (ext i))
    (p:∀i:I,G.Walk (inner i 0) (inner i (Fin.last (data.c*data.d))))
    (hp:∀i,(p i).support=List.ofFn (inner i))
    (hcycleStep:∀j∈data.t,∀k<(data.C j).length,
      factorCycleOrientation G e ((data.C j).getVert k)=(data.C j).getVert (k+1))
    (hrunStep:∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
      factorCycleOrientation G e ((data.path (.inr r)).getVert k)=(data.path (.inr r)).getVert (k+1))
    (T:SimpleGraph V) (u v:actualOldPieceIndex data→V) (q:∀z,T.Walk (u z) (v z))
    (hlen:∀z,(q z).length=(actualOldPieceWalk data z).length)
    (hdir:∀z k,k<(q z).length→((q z).getVert k,(q z).getVert (k+1))∈H)
    (hclose:∀j:{j // j∈data.t},(v (.inl j),u (.inl j))∈H):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(f:{x // x∈A}↪V),
    (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩)→
    (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
      f ⟨(actualOldPieceWalk data z).getVert k.val,
        Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
        (q z).getVert k.val)→
    ∀x y,s(x,y)∈data.deletedEdges\(Finset.univ.biUnion (fun i:I=>(p i).edges.toFinset))→
      D x y→(ψ x,ψ y)∈H:=by
  intro A f hψ hf
  have ⟨hpieces,hc⟩:=actual_matched_piece_directed_arcs data T u v q hlen (fun x y=>(x,y)∈H) hdir hclose ψ f hψ hf
  have hc':=actual_matched_cycle_directed_arcs data ψ (fun x y=>(x,y)∈H) hpieces hc
  have hr:∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
      (ψ ((data.path (.inr r)).getVert k),ψ ((data.path (.inr r)).getVert (k+1)))∈H:=by
    intro r k hk
    exact hpieces (.inr r) k hk
  have heq:(Finset.univ.biUnion (fun i:I=>(p i).edges.toFinset))=
      Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset):=
    actual_reindexed_final_edge_union data b ext inner hinner hsupp p hp
  rw [heq]
  exact actual_old_arc_host_from_selected_walks G hG e pieces D hpair hvalid hArcs halign data ψ H hcycleStep hc' hrunStep hr
end Oberwolfach
