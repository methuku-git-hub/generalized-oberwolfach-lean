module

public import Oberwolfach.LongMixedApproximateGraph
public import Oberwolfach.LongUsedRawMixedDirection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color C:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color] [Fintype C] [DecidableEq C]

theorem long_used_sampled_matching_avoids_selected
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (g:Γ) (j:Color):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (ω e)
    let T:=bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims G π d raw) (rawMarkedPairSpokes π d raw g j))
    let φ:=markedRawSampledPhysicalEmbedding G π d raw g j
    ∀(R:C→Finset {z // z∈T}) (M:Finset C),
      Disjoint (longSelectedPhysicalGraph G π d ω) (physicalRimCandidateUnion φ R M):=by
  intro raw T φ R M
  apply disjoint_iff_inf_le.mpr
  intro x y h
  have hdir:=long_used_raw_mixed_direction G π d raw g j R M x y h.2
  have ha:(longApproximatePhysicalGraph G π d ω).Adj x y:=by
    rcases hdir with hd|hd
    · exact long_raw_mixed_arc_is_approximate_edge G π d ω x y hd
    · exact (long_raw_mixed_arc_is_approximate_edge G π d ω y x hd).symm
  exact (disjoint_iff_inf_le.mp (selected_and_approximate_rim_graphs_disjoint G π d ω)) ⟨h.1,ha⟩
end Oberwolfach
