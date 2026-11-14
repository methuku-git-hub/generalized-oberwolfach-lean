module

public import Oberwolfach.LongClassDynamicCompletionSameSampleBridge
public import Oberwolfach.LongMatchedRequiredPackingReady
public import Oberwolfach.LongUsedSelectedDisjoint

@[expose] public section
/-! The dynamic completion and the actual surviving matching discharge the
full-domain correction's eligibility and close-edge coverage together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchedClassDynamicReadyFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) matchedClassDynamicReadySix : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance matchedClassDynamicReadyArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _

theorem long_matched_class_dynamic_completion_ready
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S Mhost Del)
    (hI:∀v,π v∈I↔v∈I)
    (hclass:∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d z.1).Adj x y→S.Adj x y)
    (hreserve:markedResourceRimGraph C≤longSelectedPhysicalGraph G π d z.1)
    (hU:0<Fintype.card U) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1 (Sum.inr e))) false) t)
    (H:Finset U) (absorber:U→Finset (Fin n)) (δlocal ρ₀ δglobal:ℝ)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let Tmix:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let Q:=longRawSurvivingResources G π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q Tmix (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true;
    ∀Mix:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈Tmix))) (Mix.map q)
    let Sel:=longSelectedPhysicalGraph G π d z.1
    let Req:=fun x y=>Mhost x y=1 ∧ markedPhysicalRim G π (3*d)
      (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)≠1
    let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=fun Pack:Finset (Sym2 (Fin n))=>longClassInnerRequiredRepair S Used Kbase I Pack
    let DelPlus:=Del⊔markedResourceRimGraph C;
    LongSelectedClassDynamicSourceResidualCompletion hU F G π d (r+4) ℓ raw t Jret z.1 H I S Kplus Used DelPlus absorber δlocal Extra ρ₀ θ δglobal (Mix.map q)→
    ∃(Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))),
      Pack⊆(longApproximatePhysicalGraph G π d z.1).edgeFinset ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δglobal*Fintype.card (Fin n)) ∧
      let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E;
      (∀x y,Small.Adj x y→¬(markedResourceRimGraph C).Adj x y) ∧
      (∀x y,Mhost x y=1→Used.Adj x y→longOrdinaryArcEligible π d (x,y)∨longMarkedArcEligible π d (x,y)) ∧
      longCloseRequiredGraph S π d Req (fun x y=>Used.Adj x y)≤Small ∧
      let P:=longEligibleResidualArc Mhost Small ⊥
      let T₁:=longDualInitialMarked G (fun e=>z.1 (Sum.inl e)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
      ∀T:Finset {e:(Fin n×Fin n) // P e},(∀e,e.val.1∈I→(e∈T↔e∈T₁))→
      ∀mark a b,a∈I→b∈I→
        (markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) mark a b=1 ↔
          if mark then ∃e:residualMarkedArc P T,e.val.val.1=a∧π.symm e.val.val.2=b
          else ∃e:residualOrdinaryArc P T,e.val.val.1=a∧e.val.val.2=b):=by
  intro raw ℓ R Tmix Q q φ Mix Used Sel Req Kbase Kplus DelPlus hsource
  have hdis:Disjoint Sel Used:=by
    have hdis0:=long_used_sampled_matching_avoids_selected G π d z.1 true true
      (restrictedResourceSet R (Function.Embedding.subtype (·∈Tmix))) (Mix.map q)
    convert hdis0 using 1 <;> congr! 5 <;> exact Subsingleton.elim _ _
  obtain ⟨Pack,E,hUsed,hApprox,hcover,hJ,hdegree,hSafe,hAgreement⟩:=
    long_class_dynamic_completion_same_sample_bridge Δ G π z I θ D alpha γ eps βList F hF weight w D₀ C S Del Used Mhost hw hI hclass hdis hreserve
      hU (r+4) ℓ t Jret H absorber δlocal ρ₀ δglobal Extra (Mix.map q) hsource
  have hbase:Kbase.edgeFinset⊆Finset.univ.biUnion E:=by
    intro e he
    apply hcover
    apply SimpleGraph.edgeFinset_mono (show Kbase≤Kplus Pack from le_sup_left)
    exact he
  have hready0:=long_matched_required_packing_ready Δ G π z I θ D alpha γ eps βList F hF weight w D₀ C S Del Sel Mhost hw
  have hdec:instDecidableEqFin n=matchedClassDynamicReadyFin n:=Subsingleton.elim _ _
  have hdecK:instDecidableEqFin K=matchedClassDynamicReadyFin K:=Subsingleton.elim _ _
  try rw [hdec] at hready0
  try rw [hdecK] at hready0
  have hready:=hready0 Mix Pack E hbase
  refine ⟨Pack,E,hApprox,hdegree,hSafe,hready.1,hready.2,?_⟩
  exact hAgreement
end Oberwolfach
