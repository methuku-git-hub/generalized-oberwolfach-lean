module

public import Oberwolfach.PhysicalSamplingLayerDisjoint
public import Oberwolfach.RawMixedPhysicalArcHost

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]

theorem long_raw_mixed_arc_is_approximate_edge
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (x y:V)
    (h:rawMixedPhysicalArc G π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y):
    (longApproximatePhysicalGraph G π d ω).Adj x y:=by
  let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (ω e)
  rcases h with h|h
  · let e:MarkedSampleArc G π (3*d) (fun e=>raw (Sum.inl e)) false:=⟨(x,y),h⟩
    have he:s(x,y)∈(markedSampleArcSetGraph G π d raw Finset.univ).edgeFinset:=by
      simpa only [Sum.elim_inl] using
        (markedSampleArcSetGraph_coordinate G π d raw Finset.univ (Sum.inl e)).mpr (Finset.mem_univ _)
    exact SimpleGraph.mem_edgeFinset.mp he
  · let e:MarkedSampleArc G π (3*d) (fun e=>raw (Sum.inl e)) true:=⟨(x,π.symm y),h⟩
    have he:s(x,y)∈(markedSampleArcSetGraph G π d raw Finset.univ).edgeFinset:=by
      simpa only [Sum.elim_inr,e,Equiv.apply_symm_apply] using
        (markedSampleArcSetGraph_coordinate G π d raw Finset.univ (Sum.inr e)).mpr (Finset.mem_univ _)
    exact SimpleGraph.mem_edgeFinset.mp he
end Oberwolfach
