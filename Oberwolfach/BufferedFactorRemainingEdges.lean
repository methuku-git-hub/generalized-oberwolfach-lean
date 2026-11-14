module

public import Oberwolfach.BufferedOrientedTailDomain
public import Oberwolfach.BufferedOrientedWalkDeletedEdges

@[expose] public section
/-! The source factor remaining after deleting the reserved walk edges has
exactly the physical edges indexed by the buffered complement-tail domain. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_factor_remaining_edges
    {X I:Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (hstep:∀i (p:Fin (n i)),factorCycleOrientation G e (inner i p.castSucc)=inner i p.succ)
    (p:∀i,G.Walk (inner i 0) (inner i (Fin.last (n i))))
    (hlen:∀i,(p i).length=n i) (hsupp:∀i,(p i).support=List.ofFn (inner i)):
    G.edgeFinset\(Finset.univ.biUnion (fun i=>(p i).edges.toFinset))=
      (complementTailDomain (bufferedPathFullDomain n inner) (bufferedFinalEndpoints n inner)).image
        (factorOrientedPhysicalEdge (factorCycleOrientation G e)):=by
  rw [buffered_oriented_walk_deleted_edges G n inner (factorCycleOrientation G e) hstep p hlen hsupp]
  rw [factor_edges_after_tail_deletion G hG e]
  rw [buffered_oriented_tail_domain n ext inner hinner hdis (factorCycleOrientation G e) hstep]
end Oberwolfach
