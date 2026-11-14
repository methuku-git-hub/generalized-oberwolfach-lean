module

public import Oberwolfach.OrdinaryOldArcApproximateLayer
public import Oberwolfach.ActualOldHostEmptyFinal

@[expose] public section
/-! With empty final marked index, the old source edges lie in the
approximate physical layer and therefore avoid the selected free host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_old_edges_in_approximate_layer
    {V U Γ Color X A B J:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color] [Fintype X] [DecidableEq X]
    [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    (P H Del:SimpleGraph V) (hHP:H≤P) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e);
    ∀{F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F)
    (hempty:IsEmpty A) (hs:data.s₁=firstSumIndices) (ψ:X→V),
    ActualOldImageDirected data ψ (rawMixedPhysicalArc H π d (rawMarkedDeleteRims raw Del.edgeFinset))→
    data.deletedEdges.image (Sym2.map ψ)⊆(longApproximatePhysicalGraph P π d σ).edgeFinset:=by
  intro raw F data hempty hs ψ hdir
  apply actual_old_directed_host_with_empty_final data hempty hs ψ
    (longApproximatePhysicalGraph P π d σ) (rawMixedPhysicalArc H π d (rawMarkedDeleteRims raw Del.edgeFinset))
  · intro x y h
    have hh:=raw_mixed_deleted_arc_in_approximate_layer P H Del hHP π d σ x y h
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hh
  · exact hdir

theorem selected_free_avoids_old_approximate_edges
    {V U Γ Color I:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color] (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Old:I→Finset (Sym2 V)) (hOld:∀i,Old i⊆(longApproximatePhysicalGraph P π d σ).edgeFinset)
    (Dfree:V→V→Prop) (hfree:∀x y,Dfree x y→ rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y):
    ∀i x y,Dfree x y→s(x,y)∉Old i:=by
  intro i x y hh
  exact selected_host_avoids_approximate_packing P π d σ (Old i) (hOld i) x y (hfree x y hh)
end Oberwolfach
