module

public import Oberwolfach.LongAssignedMixedSeedFamilies

@[expose] public section
/-! The prescribed marked and ordinary cycle-frequency profiles give
near-unit degree on every active resource of their common sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U CM:Type} {CO:Fin K→Type} [Fintype U] [DecidableEq U]
  [Fintype CM] [∀i,Fintype (CO i)]

theorem long_assigned_mixed_sampled_unit_degree
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (θ D p k t τ:ℝ) (ht:0≤t) (hD:0<D) (hp:0<p)
    (hb:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hpdef:p=(∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D)
    (hkdef:k=(∑u,longAssignedApproxMarkedWeight F hF K m θ u)/D)
    (RM:CM→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (RO:∀i,CO i→Finset ((Fin n×Fin n)⊕(Fin n×U)))
    (wM:CM→ℝ) (wO:∀i,CO i→ℝ)
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (hM:∀root,state root=true→
      |resourcePatternLoad RM wM (fun _ _=>true) root state-
        longAssignedMixedTarget F hF K m θ D p k none root|≤
          t+τ*longAssignedMixedTarget F hF K m θ D p k none root)
    (hO:∀i root,state (ordinaryMarkedResourceEmbedding root)=true→
      |resourcePatternLoad (RO i) (wO i) (fun _ _=>true) root
        (fun x=>state (ordinaryMarkedResourceEmbedding x))-
        longAssignedMixedTarget F hF K m θ D p k (some i) (ordinaryMarkedResourceEmbedding root)|≤
          t+τ*longAssignedMixedTarget F hF K m θ D p k (some i) (ordinaryMarkedResourceEmbedding root)):
    ∀v:{x // x∈bernoulliVertexSet state},
      |hypergraphWeightedDegree
        (restrictedResourceSet (mixedCandidateResources (longMixedSeedResources RM RO))
          (Function.Embedding.subtype (fun x=>x∈bernoulliVertexSet state)))
        (fun c=>mixedCandidateWeight (longMixedSeedWeight wM wO) c.val) v-1|≤
          ((K:ℝ)+1)*t+τ := by
  intro v
  have hload:=long_assigned_mixed_seed_component_loads F hF m θ D p k t τ ht RM RO wM wO state hM hO
  have htarget:=long_assigned_mixed_target_sum_one F hF K m θ D p k hD hp hb hpdef hkdef
  have hh:=mixed_sampled_resource_degree_from_targets (longMixedSeedResources RM RO) (longMixedSeedWeight wM wO)
    state (longAssignedMixedTarget F hF K m θ D p k) τ t htarget hload v
  convert hh using 1 <;> congr! 4 <;> simp
end Oberwolfach
