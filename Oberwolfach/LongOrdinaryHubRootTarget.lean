module

public import Oberwolfach.LongMixedHubSpokeCounts
public import Oberwolfach.LongAssignedMixedTargetProfile

@[expose] public section
/-! Every resource in the fixed ordinary-spoke set for a hub has exactly
the corresponding ordinary seed target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_ordinary_hub_root_target
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ D p k:ℝ) (i:Fin K) (u:U)
    (root:((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))
    (hroot:root∈ordinaryCommonHubSpokeRoots u):
    longAssignedMixedTarget F hF K m θ D p k (some i) root=
      longAssignedKeptOrdinaryContribution F hF K θ i u/
        longAssignedApproxOrdinaryWeight F hF K m θ u:=by
  unfold ordinaryCommonHubSpokeRoots ordinaryHubSpokeRoots at hroot
  obtain ⟨s,hs,hse⟩:=Finset.mem_map.mp hroot
  have hh:∃v,s=Sum.inr (v,u):=by
    simpa only [Finset.mem_image,Finset.mem_univ,true_and,eq_comm] using hs
  obtain ⟨v,rfl⟩:=hh
  have he:root=Sum.inr (false,v,u):=by
    simpa [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] using hse.symm
  rw [he]
  rfl
end Oberwolfach
