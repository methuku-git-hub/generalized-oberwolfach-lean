module

public import Oberwolfach.LongSelectedRetainedClassDynamicHostSameEmbeddingAllHubProof
public import Oberwolfach.LongSelectedRetainedClassDynamicSameBalancedAllHubProof
public import Oberwolfach.LongSelectedRetainedClassDynamicHostSameEmbeddingTrackedProof
public import Oberwolfach.LongSelectedRetainedClassDynamicSameBalancedTrackedLocalProof
public import Oberwolfach.LongSelectedClassDynamicHostSameEmbeddingImageLoadProof
public import Oberwolfach.LongSelectedClassDynamicSameBalancedImageLoadProof
public import Oberwolfach.LongSelectedClassDynamicHostSameEmbeddingProof
public import Oberwolfach.LongSelectedClassDynamicSameBalancedProof
public import Oberwolfach.LongClassWitnessHostCompletionInputs
public import Oberwolfach.LongClassDynamicBalancedMatchingResidual

@[expose] public section
/-! The host complement and its exact balanced degrees use the same surviving
matching and class correction witness, with the fixed reserve excluded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance classWitnessRetainedDynamicSameBalancedAllHubFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) classWitnessRetainedDynamicSameBalancedAllHubSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem long_class_witness_retained_dynamic_same_balanced_residual_all_hub
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S Mhost Del)
    (hreserve:markedResourceRimGraph C≤longSelectedPhysicalGraph G π d z.1)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hU:0<Fintype.card U) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1 (Sum.inr e))) false) t)
    (H:Finset U) (absorber:U→Finset (Fin n)) (hAbs:∀w∈H,Disjoint (absorber w) I) (δlocal ρ₀ δglobal:ℝ)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let T:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let Q:=longRawSurvivingResources G π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q T (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true;
    ∀Mix:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (Mix.map q)
    let Sel:=longSelectedPhysicalGraph G π d z.1
    let Req:=fun x y=>Mhost x y=1 ∧ markedPhysicalRim G π (3*d)
      (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)≠1
    let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=fun Pack:Finset (Sym2 (Fin n))=>longClassInnerRequiredRepair S Used Kbase I Pack
    let DelPlus:=Del⊔markedResourceRimGraph C
    let Dhost:=fun x y=>Mhost x y=1 ∧ ¬(markedResourceRimGraph C).Adj x y;
    LongSelectedRetainedClassDynamicSourceHostCompletionAllHubFull hU F G π d (r+4) ℓ raw t Jret z.1 H I S Kplus Used DelPlus absorber δlocal Dhost Extra ρ₀ θ δglobal (Mix.map q)→
    LongSelectedRetainedClassDynamicSourceSameBalancedAllHub hU F G π d (r+4) ℓ raw t Jret z.1 H I S Kplus Used DelPlus (markedResourceRimGraph C) absorber δlocal Mhost Dhost Extra ρ₀ θ δglobal (Mix.map q):=by
  intro raw ℓ R T Q q φ Mix Used Sel Req Kbase Kplus DelPlus Dhost hsource
  have hInputs:=long_class_witness_host_completion_inputs Δ G π z I θ D alpha γ eps βList F hF weight w D₀ C S Del Mhost hw hreserve Mix
  have hAvoid:∀x y,Used.Adj x y→¬(markedResourceRimGraph C).Adj x y:=by
    intro x y hu hr
    exact hInputs.2.1 x y hu (Or.inr hr)
  have hSame0:=long_selected_retained_class_dynamic_host_same_embedding_all_hub hU F hF G S π d (r+4) ℓ raw t Jret z.1 H I Kplus Used DelPlus (markedResourceRimGraph C) absorber δlocal Dhost Extra ρ₀ θ δglobal hd hInputs.1 hAbs hInputs.2.1 hInputs.2.2 hAvoid (fun x y h=>h.2)
  have hdec:longSelectedRetainedClassDynamicHostSameEmbeddingAllHubProofFin n=classWitnessRetainedDynamicSameBalancedAllHubFin n:=Subsingleton.elim _ _
  have hdecK:longSelectedRetainedClassDynamicHostSameEmbeddingAllHubProofFin K=classWitnessRetainedDynamicSameBalancedAllHubFin K:=Subsingleton.elim _ _
  try rw [hdec] at hSame0
  try rw [hdecK] at hSame0
  have hSame:=hSame0 (Mix.map q) hsource
  have hB:=long_selected_retained_class_dynamic_same_balanced_degrees_all_hub hU F hF G π d (r+4) ℓ raw t Jret z.1 H I Kplus Used DelPlus (markedResourceRimGraph C) absorber δlocal S Mhost Dhost Extra ρ₀ θ δglobal hd hnoshort (fun x y h=>h.1) hw.1 hw.2.1
  have hdec2:longRetainedClassDynamicSameBalancedAllHubProofFin n=classWitnessRetainedDynamicSameBalancedAllHubFin n:=Subsingleton.elim _ _
  have hdec2K:longRetainedClassDynamicSameBalancedAllHubProofFin K=classWitnessRetainedDynamicSameBalancedAllHubFin K:=Subsingleton.elim _ _
  try rw [hdec2] at hB
  try rw [hdec2K] at hB
  exact hB (Mix.map q) hSame
end Oberwolfach
