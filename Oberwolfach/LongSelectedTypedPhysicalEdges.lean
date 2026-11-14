module

public import Oberwolfach.LongPreparationPhysicalStates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]

theorem long_selected_ordinary_arc_is_physical_edge
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (x y:V)
    (h:markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false x y=1):
    (longSelectedPhysicalGraph G π d ω).Adj x y:=by
  let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (ω e)
  let e:MarkedSampleArc G π (3*d) (fun e=>raw (Sum.inl e)) false:=⟨(x,y),h⟩
  have he:s(x,y)∈(markedSampleArcSetGraph G π d raw Finset.univ).edgeFinset:=by
    simpa only [Sum.elim_inl] using
      (markedSampleArcSetGraph_coordinate G π d raw Finset.univ (Sum.inl e)).mpr (Finset.mem_univ _)
  exact SimpleGraph.mem_edgeFinset.mp he

theorem long_selected_marked_arc_is_physical_edge
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (x y:V)
    (h:markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true x (π.symm y)=1):
    (longSelectedPhysicalGraph G π d ω).Adj x y:=by
  let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (ω e)
  let e:MarkedSampleArc G π (3*d) (fun e=>raw (Sum.inl e)) true:=⟨(x,π.symm y),h⟩
  have he:s(x,y)∈(markedSampleArcSetGraph G π d raw Finset.univ).edgeFinset:=by
    simpa only [Sum.elim_inr,e,Equiv.apply_symm_apply] using
      (markedSampleArcSetGraph_coordinate G π d raw Finset.univ (Sum.inr e)).mpr (Finset.mem_univ _)
  exact SimpleGraph.mem_edgeFinset.mp he
end Oberwolfach
