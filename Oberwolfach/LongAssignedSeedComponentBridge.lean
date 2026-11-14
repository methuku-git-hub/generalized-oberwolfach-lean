module

public import Oberwolfach.LongAssignedMixedUnitDegree
public import Oberwolfach.MarkedOrdinaryRetainedState

@[expose] public section
/-! The separately verified marked and ordinary seed estimates feed the
same long-class profile on the actual common resource state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U CM:Type} {CO:Fin K→Type} [Fintype U] [DecidableEq U]
  [Fintype CM] [∀i,Fintype (CO i)]

theorem long_assigned_mixed_loads_from_seed_targets
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (θ D p k t τ:ℝ) (ht:0≤t)
    (RM:CM→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (RO:∀i,CO i→Finset ((Fin n×Fin n)⊕(Fin n×U)))
    (wM:CM→ℝ) (wO:∀i,CO i→ℝ)
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (hM:∀root,state root=true→
      |resourcePatternLoad RM wM (fun _ _=>true) root state-
        markedSeedRootTarget m p k (longAssignedIntervalProbability F hF K m θ)
          (longAssignedSpokeProbability F hF K m θ) true true root|≤
          t+τ*markedSeedRootTarget m p k (longAssignedIntervalProbability F hF K m θ)
            (longAssignedSpokeProbability F hF K m θ) true true root)
    (hO:∀i root,state (ordinaryMarkedResourceEmbedding root)=true→
      |resourcePatternLoad (RO i) (wO i) (fun _ _=>true) root
        (fun x=>state (ordinaryMarkedResourceEmbedding x))-
        ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
            longAssignedApproxOrdinaryWeight F hF K m θ u) root|≤
        t+τ*ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
            longAssignedApproxOrdinaryWeight F hF K m θ u) root):
    ∀i root,root∈bernoulliVertexSet state →
      |resourcePatternLoad (longMixedSeedResources RM RO i) (longMixedSeedWeight wM wO i)
        (fun _ _=>true) root state-longAssignedMixedTarget F hF K m θ D p k i root|≤
          t+τ*longAssignedMixedTarget F hF K m θ D p k i root := by
  apply long_assigned_mixed_seed_component_loads F hF m θ D p k t τ ht RM RO wM wO state
  · intro root hroot
    have hh:=hM root hroot
    rw [long_assigned_marked_seed_target F hF K m θ D p k root] at hh
    exact hh
  · intro i root hroot
    have hh:=hO i root hroot
    rw [long_assigned_ordinary_seed_target F hF K m θ D p k i root] at hh
    exact hh
end Oberwolfach
