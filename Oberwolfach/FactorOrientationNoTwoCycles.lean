module

public import Oberwolfach.FactorCycleOrientationEdges

@[expose] public section
/-! A cyclic orientation of a two-regular simple graph has no one- or
two-cycles, so each physical edge has a unique oriented representative. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_orientation_no_fixed_points {X:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (x:X):factorCycleOrientation G e x≠x:=by
  intro h
  have ha:=factor_cycle_orientation_adj G hG e x
  rw [h] at ha
  exact G.loopless.irrefl x ha

theorem factor_orientation_no_two_cycles {X:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (x:X):factorCycleOrientation G e (factorCycleOrientation G e x)≠x:=by
  classical
  intro htwo
  let σ:=factorCycleOrientation G e
  have hs:G.neighborFinset x⊆{σ x}:=by
    intro y hy
    have hxy:G.Adj x y:=(SimpleGraph.mem_neighborFinset G x y).mp hy
    rcases (factor_cycle_orientation_edge_iff G hG e x y).mp hxy with h | h
    · exact Finset.mem_singleton.mpr h.symm
    · have hyx:y=σ x:=σ.injective (h.trans htwo.symm)
      exact Finset.mem_singleton.mpr hyx
  have hc:=Finset.card_le_card hs
  rw [SimpleGraph.card_neighborFinset_eq_degree,hG x,Finset.card_singleton] at hc
  omega
end Oberwolfach
