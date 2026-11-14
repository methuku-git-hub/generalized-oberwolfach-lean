module

public import Oberwolfach.LongEarlyMatchingForResidualEmbedding
public import Oberwolfach.LongEarlyMatchingListsForDeletion
public import Oberwolfach.LongMatchingSourceCountWitness

@[expose] public section

/-! The same-deletion matching and reserved lists furnish the exact matching
and source-count input used by the first-vortex residual embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 60000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem long_early_matching_uniform_for_residual_embedding
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (r K d:ℕ) (θ D alpha γ eps ζEarly βList:ℝ)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Inner:Finset (Fin n))
    (hEarly:∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤ζEarly*n)→
      LongEarlyMatchingListsForDeletion r K d θ D alpha γ eps ζEarly βList P π F hF weight w z Inner Del):
    ∀(Del:SimpleGraph (Fin n)) (δDel:ℝ), (∀v,(Del.degree v:ℝ)≤δDel)→δDel≤ζEarly*n→
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let ℓ:=fun i=>ni i+2
    let Wm:=longAssignedMarkedSeed F hF K (r+4) d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K (r+4) d θ D P π ni hni w
    let W:=longMixedSeedWeight Wm Wo
    let Rsrc:=longRawHubResources (U:=U) π d (r+4) ℓ
    let R:=mixedCandidateResources Rsrc
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
    let state:=longRawHubState P π d raw true true
    let T:=bernoulliVertexSet state
    let e:{v // v∈S}↪_:=Function.Embedding.subtype _
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let Hret:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
    let Q:=restrictedResourceSet R e
    let hub:=longRawHubNames (U:=U) π d (r+4) ℓ;
    ∃M:Finset (RestrictedResource R e),
      (∀c∈M,0<mixedCandidateWeight W c.val) ∧
      (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
      (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (alpha*n) (γ*(longRawIncidenceSet S i).card)) ∧
      (∀j:LongRetainedHubTest F hF K θ,
        (1-γ)*(∑c:RestrictedResource R e,longRetainedHubIndicator F hF θ hub j c.val*mixedCandidateWeight W c.val)≤
          ∑c∈M,longRetainedHubIndicator F hF θ hub j c.val) ∧
      (∀j:LongRetainedHubTest F hF K θ,
        (∑c∈M,longRetainedHubIndicator F hF θ hub j c.val)≤
          (1+γ)*(∑c:RestrictedResource R e,longRetainedHubIndicator F hF θ hub j c.val*mixedCandidateWeight W c.val)) ∧
      (∀(Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U),
        MarkedFixedTerminalAbsorber P π d (r+4) selected Hret Reserve X Z →
        LongMatchingSourceCountWitness F hF π d (r+4) ℓ θ eps T (M.map q)) ∧
      LongSampleReservedLists P π d z Del Inner (βList/2) := by
  intro Del δDel hDel hcap
  exact long_early_matching_for_residual_embedding r K d θ D alpha γ eps ζEarly βList P π F hF weight w z Inner Del
    (hEarly Del (fun v=>(hDel v).trans hcap))
end Oberwolfach
