module

public import Oberwolfach.SelectedHostAvoidsApproximatePacking
public import Oberwolfach.RawMixedDeletedArcHost

@[expose] public section
/-! Surviving old directed arcs lie in the approximate physical layer on the
same expanded sample, even when the old host is a subgraph of the full host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_mixed_deleted_arc_in_approximate_layer
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P H Del:SimpleGraph V) (hHP:H≤P) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e);
    ∀x y,rawMixedPhysicalArc H π d (rawMarkedDeleteRims raw Del.edgeFinset) x y→
      s(x,y)∈(longApproximatePhysicalGraph P π d σ).edgeFinset:=by
  intro raw x y h
  rcases h with h|h
  · have h' := ((rawMarkedDeleteRims_rims H π d raw Del.edgeFinset (Sum.inl (x,y))).mp h).1
    change markedPhysicalRim H π (3*d) (fun e=>raw (Sum.inl e)) false x y=1 at h'
    have hh:=(markedPhysicalRim_eq_one_iff H π (3*d) (fun e=>raw (Sum.inl e)) false x y).mp h'
    have hP:markedPhysicalRim P π (3*d) (fun e=>raw (Sum.inl e)) false x y=1:=by
      apply (markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>raw (Sum.inl e)) false x y).mpr
      exact ⟨hh.1,hHP hh.2.1,hh.2.2⟩
    let e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false:=⟨(x,y),hP⟩
    simpa only [longApproximatePhysicalGraph,Sum.elim_inl,raw] using
      (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inl e)).mpr (Finset.mem_univ _)
  · have h' := ((rawMarkedDeleteRims_rims H π d raw Del.edgeFinset (Sum.inr (x,π.symm y))).mp h).1
    change markedPhysicalRim H π (3*d) (fun e=>raw (Sum.inl e)) true x (π.symm y)=1 at h'
    have hh:=(markedPhysicalRim_eq_one_iff H π (3*d) (fun e=>raw (Sum.inl e)) true x (π.symm y)).mp h'
    have hP:markedPhysicalRim P π (3*d) (fun e=>raw (Sum.inl e)) true x (π.symm y)=1:=by
      apply (markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>raw (Sum.inl e)) true x (π.symm y)).mpr
      exact ⟨hh.1,hHP hh.2.1,hh.2.2⟩
    let e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true:=⟨(x,π.symm y),hP⟩
    simpa only [longApproximatePhysicalGraph,Sum.elim_inr,e,Equiv.apply_symm_apply,raw] using
      (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inr e)).mpr (Finset.mem_univ _)
end Oberwolfach
