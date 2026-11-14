module

public import Oberwolfach.FactorOrientationNoTwoCycles

@[expose] public section
/-! A two-regular factor's oriented source arcs represent its physical edges
bijectively; deleting a set of tails deletes exactly the corresponding edges. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def factorOrientedPhysicalEdge {X:Type*} (σ:Equiv.Perm X) (x:X):Sym2 X:=s(x,σ x)

theorem factor_oriented_physical_edge_injective {X:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph):
    Function.Injective (factorOrientedPhysicalEdge (factorCycleOrientation G e)):=by
  intro x y h
  change s(x,factorCycleOrientation G e x)=s(y,factorCycleOrientation G e y) at h
  rcases Sym2.eq_iff.mp h with ⟨hxy,_⟩ | ⟨hxy,hyx⟩
  · exact hxy
  · have htwo:factorCycleOrientation G e (factorCycleOrientation G e y)=y:=by rw [←hxy,hyx]
    exact (factor_orientation_no_two_cycles G hG e y htwo).elim

theorem factor_edge_finset_eq_oriented {X:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph):
    G.edgeFinset=Finset.univ.image (factorOrientedPhysicalEdge (factorCycleOrientation G e)):=by
  classical
  ext s
  induction s using Sym2.inductionOn with
  | _ x y =>
    simp only [SimpleGraph.mem_edgeFinset,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · intro hxy
      rcases (factor_cycle_orientation_edge_iff G hG e x y).mp hxy with h | h
      · refine ⟨x,?_⟩
        change s(x,factorCycleOrientation G e x)=s(x,y)
        rw [h]
      · refine ⟨y,?_⟩
        change s(y,factorCycleOrientation G e y)=s(x,y)
        rw [h]
        exact Sym2.eq_swap
    · rintro ⟨x,hx⟩
      change s(x,factorCycleOrientation G e x)=s(_,_) at hx
      rw [←hx]
      exact factor_cycle_orientation_adj G hG e x

theorem factor_edges_after_tail_deletion {X:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (Y:Finset X):
    G.edgeFinset\Y.image (factorOrientedPhysicalEdge (factorCycleOrientation G e))=
      (Finset.univ\Y).image (factorOrientedPhysicalEdge (factorCycleOrientation G e)):=by
  rw [factor_edge_finset_eq_oriented G hG e,
    Finset.image_sdiff _ _ (factor_oriented_physical_edge_injective G hG e)]
end Oberwolfach
