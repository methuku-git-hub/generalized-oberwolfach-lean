module

public import Oberwolfach.OrdinaryInnerSpokeTargets

@[expose] public section
/-! The actual reference spokes and their sampled reserved-label list agree,
    so the prescribed non-reference targets avoid every reserved label. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_sample_inner_targets_avoid_reserved
    (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset V) (Hubs:Finset U) (u:U):
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
    let T:=ordinaryInnerSpokeTargets Inner Hubs Href u;
    Disjoint T (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) ∧
    T⊆Inner ∧ (T≠∅→u∈Hubs):=by
  intro Href T
  have hnot:= (ordinary_inner_spoke_targets_bounds Inner Hubs Href).2.2 u
  refine ⟨?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hr
    have hs:Href v u:=by
      apply (ordinary_reference_spoke_projection π d σ false v u).mpr
      simpa only [rawReservedSpokeList,rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and] using hr
    exact hnot v hv hs
  · intro v hv
    by_cases hu:u∈Hubs
    · have hv':v∈Inner ∧ ¬Href v u:=by
        simpa only [T,ordinaryInnerSpokeTargets,hu,ite_true,Finset.mem_filter] using hv
      exact hv'.1
    · simp [T,ordinaryInnerSpokeTargets,hu] at hv
  · intro hne
    by_contra hu
    apply hne
    simp [T,ordinaryInnerSpokeTargets,hu]
end Oberwolfach
