module

public import Oberwolfach.LongSelectedClassDynamicSourceHostCompletion
public import Oberwolfach.FirstVortexCompletionProtectsWholeReserveGeneral
public import Oberwolfach.LongWitnessClassRepairedInnerHostEncoding
public import Oberwolfach.LongClassRequiredGraphProtectsReserve

@[expose] public section
/-! From a dynamic completion using the corrected class witness, recover a
single actual packing which protects the reserve and has the exact inner
reference interface required for the fixed-reservoir completion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance classDynamicHostCompletionSameSampleFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) classDynamicHostCompletionSameSampleSix : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance classDynamicHostCompletionSameSampleArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _

theorem long_class_dynamic_host_completion_same_sample_bridge
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del Used:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S Mhost Del)
    (hI:∀v,π v∈I↔v∈I)
    (hclass:∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d z.1).Adj x y→S.Adj x y)
    (hdis:Disjoint (longSelectedPhysicalGraph G π d z.1) Used)
    (hreserve:markedResourceRimGraph C≤longSelectedPhysicalGraph G π d z.1)
    (hU:0<Fintype.card U) (m:ℕ) (ℓ:Fin K→ℕ) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1 (Sum.inr e))) false) t)
    (H:Finset U) (absorber:U→Finset (Fin n)) (δlocal ρ₀ δglobal:ℝ)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let Sel:=longSelectedPhysicalGraph G π d z.1
    let RMark:=fun x y=>markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)=1
    let Req:=fun x y=>Mhost x y=1 ∧ ¬RMark x y
    let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=fun Pack:Finset (Sym2 (Fin n))=>longClassInnerRequiredRepair S Used Kbase I Pack
    let DelPlus:=Del⊔markedResourceRimGraph C
    let Tmix:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let e:=Function.Embedding.subtype (·∈Tmix);
    ∀Mix:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedClassDynamicSourceHostCompletion hU F G π d m ℓ raw t Jret z.1 H I S Kplus Used DelPlus absorber δlocal (fun x y=>Mhost x y=1 ∧ ¬(markedResourceRimGraph C).Adj x y) Extra ρ₀ θ δglobal Mix→
    ∃(Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))),
      Pack⊆Used.edgeFinset ∧ Pack⊆(longApproximatePhysicalGraph G π d z.1).edgeFinset ∧ (Kplus Pack).edgeFinset⊆Finset.univ.biUnion E ∧
      (∀u,Disjoint (E u) ((spanningRestriction (S\Used) I\Kplus Pack).edgeFinset)) ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δglobal*Fintype.card (Fin n)) ∧
      (∀x y,(SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E).Adj x y→
        ¬(markedResourceRimGraph C).Adj x y) ∧
      let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E
      let P:=longEligibleResidualArc Mhost Small ⊥
      let T₁:=longDualInitialMarked G (fun e=>z.1 (Sum.inl e)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
      ∀T:Finset {e:(Fin n×Fin n) // P e},(∀e,e.val.1∈I→(e∈T↔e∈T₁))→
      ∀mark a b,a∈I→b∈I→
        (markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) mark a b=1 ↔
          if mark then ∃e:residualMarkedArc P T,e.val.val.1=a∧π.symm e.val.val.2=b
          else ∃e:residualOrdinaryArc P T,e.val.val.1=a∧e.val.val.2=b):=by
  intro raw Sel RMark Req Kbase Kplus DelPlus Tmix e Mix hsource
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,Eorient,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion⟩
  let Interiors:=fun w=>bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)
  let occupied:=fun w=>((data w).oldDomain\Interiors w).image (ψ w)
  let Z:=innerRequiredTargets H I (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
    (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied
  let Jbad:=spanningRestriction (S\Used) I\Kplus Pack
  let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d (fun e=>raw (Sum.inr e))) H
  let Bad:=fun v:Fin n=>Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
  let Dfree:=fun x y=>rawSelectedPhysicalRelation G π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬DelPlus.Adj x y
  let Lists:=fun w=>rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w\
    (I∪retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
  let FinalEdges:=fun w=>Finset.univ.biUnion (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset)
  have hUsedR:∀x y,Used.Adj x y→¬(markedResourceRimGraph C).Adj x y:=by
    intro x y hu hr
    exact (disjoint_iff_inf_le.mp hdis) ⟨hreserve hr,hu⟩
  let Dhost:=fun x y=>Mhost x y=1 ∧ ¬(markedResourceRimGraph C).Adj x y
  have hD:∀x y,Dhost x y→¬(markedResourceRimGraph C).Adj x y:=by
    intro x y h
    exact h.2
  obtain ⟨E,hcover,hJ,hPack,hdegree,hSafe⟩:=first_vortex_completion_whole_packing_protects_reserve_general F Dsrc _ _ data Interiors ψ
    (Kplus Pack) Jbad Used (markedResourceRimGraph C) Lbad Bad Z Dfree Dhost Pack Lists FinalEdges δglobal hUsed hUsedR hD hcompletion
  refine ⟨Pack,E,hUsed,hApprox,?_,?_,hdegree,hSafe,?_⟩
  · convert hcover using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  · intro u
    convert hJ u using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  · apply long_witness_class_repaired_inner_host_encoding Δ G π z I θ D alpha γ eps βList F hF weight w D₀ C S Del Used Mhost hw Pack E hI hclass hdis hUsed
    · intro u
      convert hJ u using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
    · convert hcover using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
