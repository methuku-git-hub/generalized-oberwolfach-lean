module

public import Oberwolfach.LongSelectedReserveClassCompletionInputs
public import Oberwolfach.LongSelectorReserveGraphBounded
public import Oberwolfach.LongFixedAbsorberSelectedRim

@[expose] public section
/-! The actual terminal absorber chosen with a valid correction can be
matched to its protected class and completion inputs on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
theorem long_absorber_all_classes_completion_from_event
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β ε:ℝ) (Qv:Vortex U G Dv β ε mm) (B:ℕ) (gammaLoss sigmaLoss:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ D alpha γ eps βList ξClass:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (hEvent:LongEveryClassValidDeletionEvent Δ G π d r gammaLoss sigmaLoss ξClass z
      (Qv.extendedVertices 1) (Qv.extendedIndices 1) K B θ D alpha γ eps βList F hF weight w)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (hvalid:D₀.Valid
      (retainedRawMarkedSpokes π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false)) z.2 false false)
      (r+4) (Qv.extendedVertices 1) (Qv.extendedIndices 1) (gammaLoss*n) (sigmaLoss*n))
    (C:MarkedSupportedEdgeSet
      (fun x:MarkedSampleArc G π (3*d) (fun e=>rawMarkedDeleteRims (fun e=>rawExpandedMarkedCollapse e (z.1 e))
        (markedSampleArcSetGraph G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)) D₀.arcs).edgeFinset (Sum.inl e)) false=>x.val.1)
      (fun x=>x.val.2)
      (fun x:MarkedSampleArc G π (3*d) (fun e=>rawMarkedDeleteRims (fun e=>rawExpandedMarkedCollapse e (z.1 e))
        (markedSampleArcSetGraph G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)) D₀.arcs).edgeFinset (Sum.inl e)) true=>x.val.1)
      (fun x=>x.val.2) π U)
    (hcard:C.edges.card≤B) (hdis:Disjoint D₀.removed C.edges)
    (Xterm:Finset (Fin n)) (Zterm:Finset U)
    (habs:MarkedFixedTerminalAbsorber G π d (r+4)
      (fun e=>rawExpandedMarkedCollapse e (z.1 e))
      (retainedRawMarkedSpokes π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false)) z.2 false false)
      C.edges Xterm Zterm):
    ∀S:SimpleGraph (Fin n),S≤G→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph G z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈Qv.extendedVertices 1,∀y∈Qv.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph G z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C.edges≤S→
      (∀x∈Qv.extendedVertices 1,∀y∈Qv.extendedVertices 1,(longSelectedPhysicalGraph G π d z.1).Adj x y→S.Adj x y) ∧
      ∃(Mhost:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)),
      LongClassMatchingDeletionWitness Δ G π d r z (Qv.extendedVertices 1) K θ D alpha γ eps βList F hF weight w D₀ C.edges S Mhost Del ∧
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let T:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let Q:=longRawSurvivingResources G π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q T (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true;
    ∀Mix:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (Mix.map q)
    let DelPlus:=Del⊔markedResourceRimGraph C.edges
    let Dhost:=fun x y=>Mhost x y=1 ∧ ¬(markedResourceRimGraph C.edges).Adj x y;
    (∀x y,Dhost x y→G.Adj x y) ∧
    (∀x y,Used.Adj x y→¬DelPlus.Adj x y) ∧
    (∀x y,rawMixedPhysicalArc G π d raw x y→¬DelPlus.Adj x y→Dhost x y) ∧
    Disjoint (longSelectedPhysicalGraph G π d z.1) Used :=by
  obtain ⟨A,hAeq,hAsample,hAcard,hclass⟩:=long_selector_bounded_reserve_graph_before_class Δ G π d r
    gammaLoss sigmaLoss ξClass z (Qv.extendedVertices 1) (Qv.extendedIndices 1) K B θ D alpha γ eps βList
    F hF weight w hEvent D₀ hvalid C hcard hdis
  have hreserve:=long_fixed_absorber_rim_is_selected G π d (r+4) z.1 false
    (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false))
    z.2 false C.edges Xterm Zterm habs
  intro S hSG hreg hedit hinner hres
  obtain ⟨hselected,Mhost,Del,hw⟩:=hclass S hSG hreg hedit hinner hres
  refine ⟨hselected,Mhost,Del,hw,?_⟩
  intro raw ℓ R T Q q φ Mix Used DelPlus Dhost
  have hbase:=long_class_witness_host_completion_inputs Δ G π z (Qv.extendedVertices 1)
    θ D alpha γ eps βList F hF weight w D₀ C.edges S Del Mhost hw hreserve Mix
  refine ⟨hbase.1,hbase.2.1,hbase.2.2,?_⟩
  exact long_used_sampled_matching_avoids_selected G π d z.1 true true
    (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (Mix.map q)
end Oberwolfach
