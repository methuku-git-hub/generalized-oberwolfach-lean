module

public import Oberwolfach.LongWitnessUsedTypeEligibility
public import Oberwolfach.LongRequiredPackingCoverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- The actual surviving matching and the prescribed packing discharge the
used-edge eligibility and required-edge coverage on the same deletion. -/
theorem long_matched_required_packing_ready
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del Sel:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z T K θ D alpha γ eps βList F hF weight w D₀ C S Mhost Del):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let Tmix:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let Q:=longRawSurvivingResources G π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q Tmix (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true
    ∀Mmix:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈Tmix))) (Mmix.map q)
    let Req:=fun x y=>Mhost x y=1 ∧ markedPhysicalRim G π (3*d)
      (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)≠1
    let Kbad:=longRequiredPhysicalGraph S (S\Used) Sel π d T Req (fun x y=>Used.Adj x y)
    ∀(Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))),
    Kbad.edgeFinset⊆Finset.univ.biUnion E→
    let Loss:=prescribedPhysicalUnion E
    let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔Loss
    (∀x y,Mhost x y=1→Used.Adj x y→longOrdinaryArcEligible π d (x,y) ∨ longMarkedArcEligible π d (x,y)) ∧
    longCloseRequiredGraph S π d Req (fun x y=>Used.Adj x y)≤Small:=by
  intro raw ℓ R Tmix Q q φ Mmix Used Req Kbad Pack E hcover Loss Small
  constructor
  · exact long_matching_witness_used_type_eligible Δ G π z T θ D alpha γ eps βList F hF weight w D₀ C S Del Mhost hw Mmix
  · have hh:=long_required_graph_covered_by_prescribed_packing S (S\Used) Sel Used π d T Req E
      (by intro e he;simpa only [Finset.mem_biUnion] using hcover he)
    intro x y h
    have hnew:=hh h
    apply Or.inr
    simpa only [Small,Loss,prescribedPhysicalUnion,SimpleGraph.fromEdgeSet_adj,Finset.mem_coe,Finset.mem_biUnion] using hnew
end Oberwolfach
