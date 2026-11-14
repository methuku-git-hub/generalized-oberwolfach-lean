module

public import Oberwolfach.ActualOldArcWalkPieces
public import Oberwolfach.ActualReindexedFinalEdgeUnion

@[expose] public section
/-! If the matched source cycles and selected runs use physical packing
edges, every old directed source edge uses that same physical packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_physical_edges_from_source_pieces
    {X V K J I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [DecidableEq K] [DecidableEq J] [Fintype I]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (pieces:List (PrescribedSourcePiece X)) (D:X→X→Prop)
    (hpair:pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀p∈pieces,p.OriginalValid D)
    (hArcs:∀x y,D x y↔(x,y)∈sourcePieceArcsUnion pieces)
    (halign:∀x,D x (factorCycleOrientation G e x))
    (data:ActualResidualData (K:=K) (J:=J) G) (ψ:X→V) (Pack:Finset (Finset V))
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
    (hcyclePack:∀j∈data.t,∀k<(data.C j).length,
      {ψ ((data.C j).getVert k),ψ ((data.C j).getVert (k+1))}∈Pack)
    (hrunPack:∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
      {ψ ((data.path (.inr r)).getVert k),ψ ((data.path (.inr r)).getVert (k+1))}∈Pack):
    ∀x y,s(x,y)∈data.deletedEdges\(Finset.univ.biUnion (fun i:I=>(p i).edges.toFinset))→
      D x y→{ψ x,ψ y}∈Pack:=by
  let H:Finset (V×V):=Finset.univ.filter (fun xy=>({xy.1,xy.2}:Finset V)∈Pack)
  have hc:∀j∈data.t,∀k<(data.C j).length,
      (ψ ((data.C j).getVert k),ψ ((data.C j).getVert (k+1)))∈H:=by
    intro j hj k hk
    simpa only [H,Finset.mem_filter,Finset.mem_univ,true_and] using hcyclePack j hj k hk
  have hr:∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
      (ψ ((data.path (.inr r)).getVert k),ψ ((data.path (.inr r)).getVert (k+1)))∈H:=by
    intro r k hk
    simpa only [H,Finset.mem_filter,Finset.mem_univ,true_and] using hrunPack r k hk
  have heq:(Finset.univ.biUnion (fun i:I=>(p i).edges.toFinset))=
      Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset):=
    actual_reindexed_final_edge_union data b ext inner hinner hsupp p hp
  intro x y hxy hd
  rw [heq] at hxy
  have hh:=actual_old_arc_host_from_selected_walks G hG e pieces D hpair hvalid hArcs halign data ψ H hcycleStep hc hrunStep hr x y hxy hd
  simpa only [H,Finset.mem_filter,Finset.mem_univ,true_and] using hh
end Oberwolfach
