module

public import Oberwolfach.EndpointFactorActualHost

@[expose] public section
/-! An endpoint factor avoiding the physical deletion graph survives in any
host containing the undeleted original edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem endpoint_factor_graph_subhost
    (Q F:SimpleGraph V) (S T:Finset V) (hST:Disjoint S T) (M:Finset (EndpointTriangle Q F S T)):
    endpointFactorGraph hST M≤Q:=by
  intro v w h
  rw [endpoint_factor_graph_triangles] at h
  obtain ⟨C,hC⟩:=SimpleGraph.iSup_adj.mp h
  have ht:=(spanningRestriction_adj ⊤ C.val.val v w).mp hC
  exact C.val.property.2.2.2.1 v ht.2.1 w ht.2.2 ht.1

theorem endpoint_factor_graph_survives_deletion
    (Q Q' F K:SimpleGraph V) (S T:Finset V) (hST:Disjoint S T) (M:Finset (EndpointTriangle Q F S T))
    (havoid:Disjoint (endpointFactorGraph hST M) K) (hkeep:Q\K≤Q'):
    endpointFactorGraph hST M≤Q':=by
  apply le_trans _ hkeep
  intro v w h
  refine ⟨endpoint_factor_graph_subhost Q F S T hST M h,?_⟩
  intro hk
  exact (disjoint_iff_inf_le.mp havoid) (v:=v) (w:=w) ⟨h,hk⟩
end Oberwolfach
