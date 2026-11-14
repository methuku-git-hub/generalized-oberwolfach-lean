module

public import Oberwolfach.LongRetainedOrdinaryInputs
public import Oberwolfach.LongAssignedSeedComponentBridge

@[expose] public section
/-! The mixed component estimates need ordinary seed estimates only for
retained lengths; all discarded components are identically zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U CM:Type} {CO:Fin K→Type} [Fintype U]
  [Fintype CM] [∀i,Fintype (CO i)]

theorem long_mixed_active_inputs_from_retained
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (θ D p k t τ:ℝ) (ht:0≤t)
    (RM:CM→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (RO:∀i,CO i→Finset ((Fin n×Fin n)⊕(Fin n×U)))
    (wM:CM→ℝ) (hub:∀i,CO i→U) (base:∀i,CO i→ℝ)
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool):
    let wO:=fun i c=>(longAssignedKeptOrdinaryContribution F hF K θ i (hub i c)/
      longAssignedApproxOrdinaryWeight F hF K m θ (hub i c))*base i c
    (∀root,state root=true→
      |resourcePatternLoad RM wM (fun _ _=>true) root state-
        markedSeedRootTarget m p k (longAssignedIntervalProbability F hF K m θ)
          (longAssignedSpokeProbability F hF K m θ) true true root|≤
          t+τ*markedSeedRootTarget m p k (longAssignedIntervalProbability F hF K m θ)
            (longAssignedSpokeProbability F hF K m θ) true true root)→
    (∀i∈longRetainedSeedIndices F hF K θ,∀root,state (ordinaryMarkedResourceEmbedding root)=true→
      |resourcePatternLoad (RO i) (wO i) (fun _ _=>true) root
          (fun x=>state (ordinaryMarkedResourceEmbedding x))-
        ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
            longAssignedApproxOrdinaryWeight F hF K m θ u) root|≤
        t+τ*ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
            longAssignedApproxOrdinaryWeight F hF K m θ u) root)→
    ∀j root,root∈bernoulliVertexSet state →
      |resourcePatternLoad (longMixedSeedResources RM RO j) (longMixedSeedWeight wM wO j)
        (fun _ _=>true) root state-longAssignedMixedTarget F hF K m θ D p k j root|≤
          t+τ*longAssignedMixedTarget F hF K m θ D p k j root :=by
  intro wO hM hret
  have hO:=long_ordinary_active_inputs_from_retained F hF m θ D p t τ ht hub base RO
    (fun x=>state (ordinaryMarkedResourceEmbedding x)) hret
  exact long_assigned_mixed_loads_from_seed_targets F hF m θ D p k t τ ht RM RO wM wO state hM hO
end Oberwolfach
