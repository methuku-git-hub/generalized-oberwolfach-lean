module

public import Oberwolfach.ActualOldArcsFromReservedParents
public import Oberwolfach.ActualParentGlobalOrientation
public import Oberwolfach.ActualReindexedFinalEdgeUnion

@[expose] public section
/-! The source-direction condition for the old selected runs follows from the
original reserved-block allocation and the globally aligned component orders. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_arc_host_from_reindexed_buffered_paths
    {X V K J I R:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J] [Fintype I] [Fintype R]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (pieces:List (PrescribedSourcePiece X)) (D:X→X→Prop)
    (hpair:pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀p∈pieces,p.OriginalValid D)
    (hArcs:∀x y,D x y↔(x,y)∈sourcePieceArcsUnion pieces)
    (halign:∀x,D x (factorCycleOrientation G e x))
    (data:ActualResidualData (K:=K) (J:=J) G) (ψ:X→V) (H:Finset (V×V))
    (components:I↪G.ConnectedComponent)
    (index:{i // i∈data.s₂}→LongReservedBlockIndex G components data.c data.d)
    (hparent:∀i:{i // i∈data.s₂},(data.P i.val).support=List.ofFn
      (longReservedSigmaBlock G components data.c data.d (fun j=>e (components j)) (index i) data.d (le_refl _)))
    (b:R≃{i // i∈data.s₁})
    (ext:∀i:R,Fin (data.c*data.d+5)↪X)
    (inner:∀i:R,Fin (data.c*data.d+1)↪X)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hsupp:∀i,(data.P (b i).val).support=List.ofFn (ext i))
    (p:∀i:R,G.Walk (inner i 0) (inner i (Fin.last (data.c*data.d))))
    (hp:∀i,(p i).support=List.ofFn (inner i))
    (hcycleStep:∀j∈data.t,∀k<(data.C j).length,
      factorCycleOrientation G e ((data.C j).getVert k)=(data.C j).getVert (k+1))
    (hcycleTarget:∀j∈data.t,∀k<(data.C j).length,
      (ψ ((data.C j).getVert k),ψ ((data.C j).getVert (k+1)))∈H)
    (hparentTarget:∀i∈data.s₂,∀r∈selectedSegmentRuns data.d (data.T i),∀k,
      2+data.c*r.1≤k→k<2+data.c*(r.2+1)→
      (ψ ((data.P i).getVert k),ψ ((data.P i).getVert (k+1)))∈H):
    ∀x y,s(x,y)∈data.deletedEdges\(Finset.univ.biUnion
      (fun i:R=>(p i).edges.toFinset))→
      D x y→(ψ x,ψ y)∈H:=by
  have heq:(Finset.univ.biUnion (fun i:R=>(p i).edges.toFinset))=
      Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset):=
    actual_reindexed_final_edge_union data b ext inner hinner hsupp p hp
  rw [heq]
  exact actual_old_arc_host_from_reserved_parents G hG e pieces D hpair hvalid hArcs halign data ψ H components index hparent hcycleStep hcycleTarget hparentTarget
end Oberwolfach
