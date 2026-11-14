module

public import Oberwolfach.LongClassWitnessRepairHostInputs
public import Oberwolfach.LongSurvivingUsedAvoidsReserve

@[expose] public section
/-! The actual surviving matching and class witness provide all orientation
and deletion-avoidance inputs for the reserve-restricted host complement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance classWitnessHostCompletionInputsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) classWitnessHostCompletionInputsSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem long_class_witness_host_completion_inputs
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S Mhost Del)
    (hreserve:markedResourceRimGraph C≤longSelectedPhysicalGraph G π d z.1):
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
    (∀x y,rawMixedPhysicalArc G π d raw x y→¬DelPlus.Adj x y→Dhost x y):=by
  intro raw ℓ R T Q q φ Mix Used DelPlus Dhost
  obtain ⟨hphys,hbal,hD,hsub,hcorrect,hdeg,hprot,hsel,hK,hhost,hmix,hlists⟩:=hw
  have hav:=long_surviving_used_avoids_deletion_and_reserve G Del (markedResourceRimGraph C) π d (r+4) ℓ z.1 hreserve Mix
  refine ⟨?_,?_,?_⟩
  · intro x y h
    exact hhost x y h.1
  · intro x y h
    exact hav x y h
  · intro x y ha hd
    refine ⟨hmix x y ha (fun h=>hd (Or.inl h)),fun h=>hd (Or.inr h)⟩
end Oberwolfach
