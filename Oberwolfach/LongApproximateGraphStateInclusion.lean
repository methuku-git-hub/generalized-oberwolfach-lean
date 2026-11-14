module

public import Oberwolfach.PhysicalSamplingLayerDisjoint
public import Oberwolfach.LongActualPhysicalGraphsInHost

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]

/-- The actual old approximate packing is contained in the states 2 and 3. -/
theorem long_approximate_graph_in_state_graph
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    longApproximatePhysicalGraph G π d ω≤longPhysicalStateGraph G ω {2,3}:=by
  intro x y h
  have hg:=long_approximate_physical_graph_le_host G π d ω h
  obtain ⟨b,o,hraw⟩:=marked_sample_graph_edge_has_physical_state G π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y h
  refine ⟨hg,?_⟩
  simp only [rawExpandedApproximateCollapse] at hraw
  rcases hx:ω (Sum.inl s(x,y)) with ⟨state,bit⟩
  fin_cases state <;> simp_all [markedExpandedApproximateCollapse]
end Oberwolfach
