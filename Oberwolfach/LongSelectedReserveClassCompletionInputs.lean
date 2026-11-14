module

public import Oberwolfach.LongClassWitnessHostCompletionInputs
public import Oberwolfach.LongUsedSelectedDisjoint

@[expose] public section
/-! The selected class, correction, reserve and actual matching witness yield
the orientation and avoidance inputs for completion on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_selected_reserve_class_completion_inputs
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ D alpha γ eps βList ξClass:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hreserve:markedResourceRimGraph C≤longSelectedPhysicalGraph G π d z.1)
    (hclass:∃S:SimpleGraph (Fin n),S≤G ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀v,((changed ((longPhysicalStateGraph G z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
      (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph G z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph C≤S ∧
      (∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d z.1).Adj x y→S.Adj x y) ∧
      ∃Mhost:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
        LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S Mhost Del):
    ∃(S:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)),
      S≤G ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀v,((changed ((longPhysicalStateGraph G z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
      (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph G z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph C≤S ∧
      (∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d z.1).Adj x y→S.Adj x y) ∧
      LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S Mhost Del ∧
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let T:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let Q:=longRawSurvivingResources G π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q T (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true;
    ∀Mix:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (Mix.map q)
    let DelPlus:=Del⊔markedResourceRimGraph C
    let Dhost:=fun x y=>Mhost x y=1 ∧ ¬(markedResourceRimGraph C).Adj x y;
    (∀x y,Dhost x y→G.Adj x y) ∧
    (∀x y,Used.Adj x y→¬DelPlus.Adj x y) ∧
    (∀x y,rawMixedPhysicalArc G π d raw x y→¬DelPlus.Adj x y→Dhost x y) ∧
    Disjoint (longSelectedPhysicalGraph G π d z.1) Used :=by
  obtain ⟨S,hSG,hreg,hedit,hinner,hres,hsel,Mhost,Del,hw⟩:=hclass
  refine ⟨S,Mhost,Del,hSG,hreg,hedit,hinner,hres,hsel,hw,?_⟩
  intro raw ℓ R T Q q φ Mix Used DelPlus Dhost
  have hbase:=long_class_witness_host_completion_inputs Δ G π z I θ D alpha γ eps βList F hF weight w D₀ C S Del Mhost hw hreserve Mix
  refine ⟨hbase.1,hbase.2.1,hbase.2.2,?_⟩
  have hdis:=long_used_sampled_matching_avoids_selected G π d z.1 true true
    (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (Mix.map q)
  exact hdis
end Oberwolfach
