module

public import Oberwolfach.RestrictedSampledRootLoads
public import Oberwolfach.MixedApproximateResourceAggregation

@[expose] public section
/-! The sampled union of candidate families has precisely the sum of the
original root-omitted loads, with the same weights and common sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
  {E:I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem mixed_sampled_resource_degree_eq_sum
    (R:∀i,E i→Finset V) (w:∀i,E i→ℝ) (σ:V→Bool)
    (v:{x:V // x∈bernoulliVertexSet σ}):
    hypergraphWeightedDegree
      (restrictedResourceSet (mixedCandidateResources R)
        (Function.Embedding.subtype (fun x=>x∈bernoulliVertexSet σ)))
      (fun c=>mixedCandidateWeight w c.val) v =
      ∑i,resourcePatternLoad (R i) (w i) (fun _ _=>true) v.val σ := by
  rw [sampled_resource_degree_eq_pattern]
  unfold resourcePatternLoad mixedCandidateResources mixedCandidateWeight
  rw [Fintype.sum_sigma]

theorem mixed_sampled_resource_codegree_bound
    (R:∀i,E i→Finset V) (w:∀i,E i→ℝ) (σ:V→Bool) (K:I→ℝ) (n:ℝ)
    (hw:∀i c,0≤w i c)
    (hcodeg:∀i (u v:V),u≠v→
      resourceOmittedPairWeight (R i) (w i) u v≤K i/n)
    (u v:{x:V // x∈bernoulliVertexSet σ}) (huv:u≠v):
    (∑c:RestrictedResource (mixedCandidateResources R)
      (Function.Embedding.subtype (fun x=>x∈bernoulliVertexSet σ)),
      if u∈restrictedResourceSet (mixedCandidateResources R)
          (Function.Embedding.subtype (fun x=>x∈bernoulliVertexSet σ)) c ∧
         v∈restrictedResourceSet (mixedCandidateResources R)
          (Function.Embedding.subtype (fun x=>x∈bernoulliVertexSet σ)) c
      then mixedCandidateWeight w c.val else 0) ≤ (∑i,K i)/n := by
  calc
    _ ≤ resourceOmittedPairWeight (mixedCandidateResources R) (mixedCandidateWeight w) u.val v.val :=
      restricted_resource_codegree_le _ _ _ (fun c : Σi,E i=>hw c.1 c.2) u v huv
    _ = ∑i,resourceOmittedPairWeight (R i) (w i) u.val v.val := by
      unfold resourceOmittedPairWeight mixedCandidateResources mixedCandidateWeight
      rw [Fintype.sum_sigma]
    _ ≤ _ := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun i _=>hcodeg i u.val v.val (fun h=>huv (Subtype.ext h)))
/-- The component load estimates combine at each active root without
changing the target profiles or the shared sampled outcome. -/
theorem mixed_sampled_resource_degree_from_targets
    (R:∀i,E i→Finset V) (w:∀i,E i→ℝ) (σ:V→Bool)
    (target:I→V→ℝ) (τ t:ℝ)
    (htarget:∀v,∑i,target i v=1)
    (hload:∀i v, v∈bernoulliVertexSet σ →
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) v σ-target i v|≤t+τ*target i v)
    (v:{x:V // x∈bernoulliVertexSet σ}):
    |hypergraphWeightedDegree
      (restrictedResourceSet (mixedCandidateResources R)
        (Function.Embedding.subtype (fun x=>x∈bernoulliVertexSet σ)))
      (fun c=>mixedCandidateWeight w c.val) v-1|≤(Fintype.card I:ℝ)*t+τ := by
  rw [mixed_sampled_resource_degree_eq_sum]
  exact finite_combined_unit_load (fun i=>target i v.val)
    (fun i=>resourcePatternLoad (R i) (w i) (fun _ _=>true) v.val σ)
    τ t (htarget v.val) (fun i=>hload i v.val v.property)
end Oberwolfach
