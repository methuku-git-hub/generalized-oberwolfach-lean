module

public import Oberwolfach.ActualOldArcsFromParentWalks
public import Oberwolfach.ActualParentGlobalOrientation

@[expose] public section
/-! The source-direction condition for the old selected runs follows from the
original reserved-block allocation and the globally aligned component orders. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_arc_host_from_reserved_parents
    {X V K J I:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J] [Fintype I]
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
    (hcycleStep:∀j∈data.t,∀k<(data.C j).length,
      factorCycleOrientation G e ((data.C j).getVert k)=(data.C j).getVert (k+1))
    (hcycleTarget:∀j∈data.t,∀k<(data.C j).length,
      (ψ ((data.C j).getVert k),ψ ((data.C j).getVert (k+1)))∈H)
    (hparentTarget:∀i∈data.s₂,∀r∈selectedSegmentRuns data.d (data.T i),∀k,
      2+data.c*r.1≤k→k<2+data.c*(r.2+1)→
      (ψ ((data.P i).getVert k),ψ ((data.P i).getVert (k+1)))∈H):
    ∀x y,s(x,y)∈data.deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))→
      D x y→(ψ x,ψ y)∈H:=by
  apply actual_old_arc_host_from_selected_parents G hG e pieces D hpair hvalid hArcs halign data ψ H hcycleStep hcycleTarget
  · intro i hi
    exact parent_walk_follows_global_reserved_orientation G hG components e data.c data.d (index ⟨i,hi⟩) data.d (le_refl _)
      (data.P i) (data.hlen i (Finset.mem_union_right _ hi)) (hparent ⟨i,hi⟩)
  · exact hparentTarget
end Oberwolfach
