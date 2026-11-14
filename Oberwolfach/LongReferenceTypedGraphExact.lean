module

public import Oberwolfach.LongReferenceResidualTypedGraphs

@[expose] public section
/-! The reference type graphs are exactly the ordinary and marked physical
rim graphs of the original selected sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance referenceTypedExactDecEq : DecidableEq V := Classical.decEq V

theorem long_reference_typed_graph_exact
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (mark:Bool) (x y:V):
    (longReferenceTypedGraph G π d ω mark).Adj x y ↔
      if mark then
        markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true x (π.symm y)=1 ∨
        markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true y (π.symm x)=1
      else
        markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false x y=1 ∨
        markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false y x=1:=by
  let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (ω e)
  have hOrd:∀a b,markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false a b=1→
      (longSelectedPhysicalGraph G π d ω).Adj a b:=by
    intro a b hr
    let e:MarkedSampleArc G π (3*d) (fun z=>raw (Sum.inl z)) false:=⟨(a,b),hr⟩
    have he:s(a,b)∈(markedSampleArcSetGraph G π d raw Finset.univ).edgeFinset:=by
      simpa only [Sum.elim_inl] using
        (markedSampleArcSetGraph_coordinate G π d raw Finset.univ (Sum.inl e)).mpr (Finset.mem_univ _)
    exact SimpleGraph.mem_edgeFinset.mp he
  have hMark:∀a b,markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true a (π.symm b)=1→
      (longSelectedPhysicalGraph G π d ω).Adj a b:=by
    intro a b hr
    let e:MarkedSampleArc G π (3*d) (fun z=>raw (Sum.inl z)) true:=⟨(a,π.symm b),hr⟩
    have he:s(a,b)∈(markedSampleArcSetGraph G π d raw Finset.univ).edgeFinset:=by
      simpa only [Sum.elim_inr,e,Equiv.apply_symm_apply] using
        (markedSampleArcSetGraph_coordinate G π d raw Finset.univ (Sum.inr e)).mpr (Finset.mem_univ _)
    exact SimpleGraph.mem_edgeFinset.mp he
  constructor
  · intro h
    exact h.2
  · intro h
    cases mark with
    | false =>
      rcases h with h|h
      · exact ⟨hOrd x y h,Or.inl h⟩
      · exact ⟨(hOrd y x h).symm,Or.inr h⟩
    | true =>
      rcases h with h|h
      · exact ⟨hMark x y h,Or.inl h⟩
      · exact ⟨(hMark y x h).symm,Or.inr h⟩
end Oberwolfach
