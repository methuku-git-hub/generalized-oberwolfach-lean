module

public import Oberwolfach.OrdinaryExpandedSharedSampleEvents

@[expose] public section
/-! The reference graph is literally the state-zero subgraph of the class
on the common expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem ordinary_shared_sample_reference_graph_eq_state_zero
    (P:SimpleGraph V)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e)) =
      longPhysicalStateGraph P σ {0} :=by
  ext x y
  simp [rawWheelGraph,retainedGraph,longPhysicalStateGraph,expandedOrdinarySelectedCollapse]

theorem ordinary_shared_sample_reference_graph_le_class
    (P:SimpleGraph V)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e)) ≤
      longPhysicalStateGraph P σ {0,1,2,3,4} :=by
  rw [ordinary_shared_sample_reference_graph_eq_state_zero]
  intro x y h
  exact ⟨h.1, by simpa using Or.inl (Finset.mem_singleton.mp h.2)⟩
end Oberwolfach
