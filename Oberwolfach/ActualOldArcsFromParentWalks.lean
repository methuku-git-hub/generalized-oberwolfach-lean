module

public import Oberwolfach.ActualOldArcWalkPieces
public import Oberwolfach.ActualSelectedRunInheritsRelation

@[expose] public section
/-! Old selected-run arcs inherit directedness and host containment from the
same buffered parents used in the actual residual data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_arc_host_from_selected_parents
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (pieces:List (PrescribedSourcePiece X)) (D:X→X→Prop)
    (hpair:pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀p∈pieces,p.OriginalValid D)
    (hArcs:∀x y,D x y↔(x,y)∈sourcePieceArcsUnion pieces)
    (halign:∀x,D x (factorCycleOrientation G e x))
    (data:ActualResidualData (K:=K) (J:=J) G) (ψ:X→V) (H:Finset (V×V))
    (hcycleStep:∀j∈data.t,∀k<(data.C j).length,
      factorCycleOrientation G e ((data.C j).getVert k)=(data.C j).getVert (k+1))
    (hcycleTarget:∀j∈data.t,∀k<(data.C j).length,
      (ψ ((data.C j).getVert k),ψ ((data.C j).getVert (k+1)))∈H)
    (hparentStep:∀i∈data.s₂,∀k<(data.P i).length,
      factorCycleOrientation G e ((data.P i).getVert k)=(data.P i).getVert (k+1))
    (hparentTarget:∀i∈data.s₂,∀r∈selectedSegmentRuns data.d (data.T i),∀k,
      2+data.c*r.1≤k→k<2+data.c*(r.2+1)→
      (ψ ((data.P i).getVert k),ψ ((data.P i).getVert (k+1)))∈H):
    ∀x y,s(x,y)∈data.deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))→
      D x y→(ψ x,ψ y)∈H:=by
  apply actual_old_arc_host_from_selected_walks G hG e pieces D hpair hvalid hArcs halign data ψ H hcycleStep hcycleTarget
  · exact actual_selected_run_inherits_parent_relation data (fun x y=>factorCycleOrientation G e x=y) hparentStep
  · exact actual_selected_run_inherits_selected_parent_relation data (fun x y=>(ψ x,ψ y)∈H) hparentTarget
end Oberwolfach
