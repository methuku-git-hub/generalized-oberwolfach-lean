module

public import Oberwolfach.ActualOldImageDirected
public import Oberwolfach.ActualOldArcWalkPieces
public import Oberwolfach.ActualParentGlobalOrientation
public import Oberwolfach.ActualSelectedRunInheritsRelation

@[expose] public section
/-! The actual directed cycle and run images discharge old-arc containment
for the original globally oriented source factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_arc_host_from_directed_images
    {X V K J I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [DecidableEq K] [DecidableEq J] [Fintype I]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (E:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (pieces:List (PrescribedSourcePiece X)) (D:X→X→Prop)
    (hpair:pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀p∈pieces,p.OriginalValid D)
    (hArcs:∀x y,D x y↔(x,y)∈sourcePieceArcsUnion pieces)
    (halign:∀x,D x (factorCycleOrientation G E x))
    (data:ActualResidualData (K:=K) (J:=J) G) (ψ:X→V)
    (components:I↪G.ConnectedComponent)
    (index:{i // i∈data.s₂}→LongReservedBlockIndex G components data.c data.d)
    (hparent:∀i:{i // i∈data.s₂},(data.P i.val).support=List.ofFn
      (longReservedSigmaBlock G components data.c data.d (fun j=>E (components j)) (index i) data.d (le_refl _)))
    (hcycleStep:∀j∈data.t,∀k<(data.C j).length,
      factorCycleOrientation G E ((data.C j).getVert k)=(data.C j).getVert (k+1))
    (R:V→V→Prop) (himage:ActualOldImageDirected data ψ R):
    ∀x y,s(x,y)∈data.deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))→
      D x y→R (ψ x) (ψ y):=by
  let H:Finset (V×V):=Finset.univ.filter (fun e=>R e.1 e.2)
  have hrunStep:∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
      factorCycleOrientation G E ((data.path (.inr r)).getVert k)=(data.path (.inr r)).getVert (k+1):=by
    apply actual_selected_run_inherits_parent_relation data (fun x y=>factorCycleOrientation G E x=y)
    intro i hi
    exact parent_walk_follows_global_reserved_orientation G hG components E data.c data.d (index ⟨i,hi⟩)
      data.d (le_refl _) (data.P i) (data.hlen i (Finset.mem_union_right _ hi)) (hparent ⟨i,hi⟩)
  have hc:∀j∈data.t,∀k<(data.C j).length,
      (ψ ((data.C j).getVert k),ψ ((data.C j).getVert (k+1)))∈H:=by
    intro j hj k hk
    simpa only [H,Finset.mem_filter,Finset.mem_univ,true_and] using himage.1 j hj k hk
  have hr:∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
      (ψ ((data.path (.inr r)).getVert k),ψ ((data.path (.inr r)).getVert (k+1)))∈H:=by
    intro r k hk
    simpa only [H,Finset.mem_filter,Finset.mem_univ,true_and] using himage.2 r k hk
  intro x y he hd
  have hh:=actual_old_arc_host_from_selected_walks G hG E pieces D hpair hvalid hArcs halign data ψ H hcycleStep hc hrunStep hr x y he hd
  simpa only [H,Finset.mem_filter,Finset.mem_univ,true_and] using hh
end Oberwolfach
