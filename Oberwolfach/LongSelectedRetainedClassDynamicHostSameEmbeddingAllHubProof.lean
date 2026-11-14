module

public import Oberwolfach.LongSelectedRetainedClassDynamicHostSameEmbeddingAllHub
public import Oberwolfach.ActualRetainedCompletionInnerAgreementAllHubTargets
public import Oberwolfach.ActualAllHubCompletionNoNewSpokes
public import Oberwolfach.LongRetainedProtectedInnerTargets
public import Oberwolfach.LongSelectedRetainedClassDynamicSourceHostCompletionTracked
public import Oberwolfach.LongSelectedRetainedClassDynamicHostSameEmbeddingTracked
public import Oberwolfach.ActualResidualSameDirectedComplementImageLoadTracked
public import Oberwolfach.ActualRetainedCompletionInnerAgreement
public import Oberwolfach.ActualSumEndpointAgreement
public import Oberwolfach.LongSelectedRetainedClassDynamicSourceHostCompletionTracked
public import Oberwolfach.LongSelectedClassDynamicHostSameEmbeddingImageLoad
public import Oberwolfach.ActualResidualSameDirectedComplementWithImageLoad
public import Oberwolfach.LongSelectedClassDynamicSourceHostSameEmbedding
public import Oberwolfach.ActualResidualSameDirectedComplement
public import Oberwolfach.LongSelectedClassDynamicSourceHostCompletion
public import Oberwolfach.LongSelectedClassDynamicSourceHostComplement
public import Oberwolfach.LongSelectedClassOrientedSourceHostCompletion
public import Oberwolfach.LongSelectedClassOrientedSourceHostComplement
public import Oberwolfach.ActualResidualDirectedComplement
public import Oberwolfach.LongSelectedOrientedSourceComplement
public import Oberwolfach.LongSelectedOrientedSourceResidualCompletion
public import Oberwolfach.LongSelectedProtectedSourceComplement
public import Oberwolfach.RetainedMarkedRootUniformity
public import Oberwolfach.LongSelectedAlignedSourceComplement
public import Oberwolfach.LongActualPhysicalGraphsInHost
public import Oberwolfach.FactorCycleOrientationEdges

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longSelectedRetainedClassDynamicHostSameEmbeddingAllHubProofFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_selected_retained_class_dynamic_host_same_embedding_all_hub
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P Sclass:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used DelG Reserve:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δ:ℝ) (Dhost:Fin n→Fin n→Prop) (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal:ℝ)
    (hd:2≤d) (hHostPhysical:∀x y,Dhost x y→P.Adj x y)
    (hAbs:∀w∈H,Disjoint (absorber w) A)
    (hUsedAvoid:∀x y,Used.Adj x y→¬DelG.Adj x y)
    (hSampleHost:∀x y,rawMixedPhysicalArc P π d raw x y→¬DelG.Adj x y→Dhost x y)
    (hUsedReserve:∀x y,Used.Adj x y→¬Reserve.Adj x y) (hDReserve:∀x y,Dhost x y→¬Reserve.Adj x y):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedRetainedClassDynamicSourceHostCompletionAllHubFull hU F P π d m ℓ raw t Jret σ H A Sclass Kbad Used DelG absorber δ Dhost Extra ρ₀ θ δglobal M →
    LongSelectedRetainedClassDynamicSourceHostSameEmbeddingAllHub hU F P π d m ℓ raw t Jret σ H A Sclass Kbad Used DelG Reserve absorber δ Dhost Extra ρ₀ θ δglobal M :=by
  intro T e M hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  have hdec0 : selectedRetainedClassDynamicHostCompletionAllHubFullFin n = longSelectedRetainedClassDynamicHostSameEmbeddingAllHubProofFin n := Subsingleton.elim _ _
  have hdec0K : selectedRetainedClassDynamicHostCompletionAllHubFullFin K = longSelectedRetainedClassDynamicHostSameEmbeddingAllHubProofFin K := Subsingleton.elim _ _
  have hdec1 : selectedRetainedClassDynamicHostSameEmbeddingAllHubFin n = longSelectedRetainedClassDynamicHostSameEmbeddingAllHubProofFin n := Subsingleton.elim _ _
  have hdec1K : selectedRetainedClassDynamicHostSameEmbeddingAllHubFin K = longSelectedRetainedClassDynamicHostSameEmbeddingAllHubProofFin K := Subsingleton.elim _ _
  try rw [hdec0] at hsource
  try rw [hdec0K] at hsource
  try rw [hdec1]
  try rw [hdec1K]
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,⟨hcapacityAll,hglobalAll⟩,hcompletion⟩
  let Interiors:=fun w=>bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)
  let occupied:=fun w=>((data w).oldDomain\Interiors w).image (ψ w)
  let AbsAll:=fun w=>if w∈H then absorber w else ∅
  let Z:=innerRequiredTargets Finset.univ A (fun w=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w))
    (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) AbsAll occupied
  let Jbad:=spanningRestriction (Sclass\Used) A\(Kbad Pack)
  let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d (fun e=>raw (Sum.inr e))) H
  let Bad:=fun v:Fin n=>Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
  let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬DelG.Adj x y
  let Dstar:=Dhost
  let Lists:=fun w=>rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w\
    (A∪retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
  have hPackP:Pack⊆P.edgeFinset:=by
    intro edge he
    have hh:=hApprox he
    exact SimpleGraph.edgeFinset_mono (long_approximate_physical_graph_le_host P π d σ) hh
  have hDstar:∀x y,Dstar x y→P.Adj x y:=hHostPhysical
  have hOldDirected:∀w,ActualOldArcContainment (data w) (ψ w) (E w) (rawMixedPhysicalArc P π d raw):=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hh⟩
    exact hh.2
  have hValid':∀w p,p∈orig w→p.OriginalValid (Dsrc w):=by
    intro w p hp
    obtain ⟨a,xs,rfl,hv⟩:=hValid w p hp
    exact hv
  have hOldHost:∀w x y,s(x,y)∈(data w).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))→Dsrc w x y→Dhost (ψ w x) (ψ w y):=by
    intro w x y he hsrc
    have hDir:=hOldDirected w (orig w) (Dsrc w) (hPair w) (hValid' w) (hArcs w) (hAlign w) x y he hsrc
    have hPackEdge:s(ψ w x,ψ w y)∈Pack:=by
      apply hOldPack w
      exact Finset.mem_image.mpr ⟨s(x,y),he,by simp⟩
    have hUsedEdge:Used.Adj (ψ w x) (ψ w y):=SimpleGraph.mem_edgeFinset.mp (hUsed hPackEdge)
    exact hSampleHost _ _ hDir (hUsedAvoid _ _ hUsedEdge)
  have hOrient:∀w x y,(F w).Adj x y→Dsrc w x y ∨ Dsrc w y x:=by
    intro w x y h
    rcases (factor_cycle_orientation_edge_iff (F w) (hF w) (E w) x y).mp h with hh|hh
    · left; simpa [hh] using hAlign w x
    · right; simpa [hh] using hAlign w y
  have hCycle:∀w,(data w).t.biUnion (fun j=>((data w).C j).support.toFinset)⊆(data w).Cembed:=by
    intro w;rw [(hprops w).2.2.2.1]
  let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val
  have hY:∀w,Y w=retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w:=by
    intro w
    ext v
    simpa only [Y,retainedFinalMarkedAt,Finset.mem_filter,Finset.mem_univ,true_and] using
      retained_marked_root_membership π d (by omega) (fun e=>raw (Sum.inr e)) false t Jret w v
  have hYBad:∀w v,v∈Y w→w∈Bad v:=by
    intro w v hv
    simp only [Bad,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [←hY w]
    exact hv
  have hZY:∀w,Disjoint (Z w) (Y w):=by
    intro w
    apply Finset.disjoint_left.mpr
    intro v hv hy
    simp only [Z,innerRequiredTargets,Finset.mem_univ,if_true,Finset.mem_sdiff,Finset.mem_union] at hv
    exact hv.2 (Or.inl (Or.inl (Or.inr ((hY w) ▸ hy))))
  have hLY:∀w,Disjoint (Lists w) (Y w):=by
    intro w
    apply Finset.disjoint_left.mpr
    intro v hv hy
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right A ((hY w) ▸ hy))
  have hOldAvoid:∀w x,x∈(data w).oldDomain→x∉bufferedPathFullDomain (fun _=>(m+1)*d) (inner w)→ψ w x∉Y w:=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,havoid,_,_⟩
    exact havoid
  have hsub:∀w,Z w⊆innerRequiredTargets Finset.univ A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
      (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) AbsAll occupied w := by
    exact (long_retained_protected_inner_targets π d (fun e=>raw (Sum.inr e)) t Jret Finset.univ A
      (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) AbsAll occupied).2.1
  have hglobal':∀v,((Finset.univ.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      (Kbad Pack).degree v+((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δglobal*n := by
    intro v
    have hh:(Finset.univ.filter (fun w=>v∈Z w)).card≤
        (Finset.univ.filter (fun w=>v∈innerRequiredTargets Finset.univ A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
          (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) AbsAll occupied w)).card := by
      apply Finset.card_le_card
      intro w hw
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
      exact hsub w hw
    have hc:=hglobalAll v
    have hr:((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤
        ((Finset.univ.filter (fun w=>v∈innerRequiredTargets Finset.univ A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
          (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) AbsAll occupied w)).card:ℝ):=by exact_mod_cast hh
    linarith
  have hComplement:=actual_residual_completion_same_directed_complement_with_image_load_and_tracked_witness
    (fun w=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w)
    (fun w=>{a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
    (fun w=>{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w})
    F hF P Dsrc data (m+1) d (fun w=>(hprops w).1) (fun w=>(hprops w).2.1)
    (fun w=>(hprops w).2.2.1) ext inner (fun w=>(hprops w).2.2.2.2.1)
    (fun w=>(hprops w).2.2.2.2.2.1) hCycle ψ (Kbad Pack) Jbad Lbad Bad Z Dfree Dstar Pack Lists δglobal ((ρ₀/4)/40000) hOldPack hPackP hOrient hDstar hOldHost Y hYBad hZY hLY Used Reserve hUsed hUsedReserve hDReserve hOldAvoid (by simpa only [Fintype.card_fin] using hglobal') hcompletion
  have hdec2 : actualResidualSameDirectedImageWitnessTrackedFin n = longSelectedRetainedClassDynamicHostSameEmbeddingAllHubProofFin n := Subsingleton.elim _ _
  try rw [hdec2] at hComplement
  rcases hComplement with ⟨piecesNew,Φ,fC,assignNew,orient,BB,g,hMcap,hgraphNew,hC,hR,hZ,hImage,hYavoid,hDirected,hHost,hPacked,hKcover,hJavoid,hPackAvoid,hEunion,hLoss,hReserve,hBB,hEndList,hag,hfree⟩
  have hEnds:∀w,
      (∀i (hp:inner w i 0∉Interiors w),fC w ⟨inner w i 0,hp⟩=i.val) ∧
      (∀i (hp:inner w i (Fin.last ((m+1)*d))∉Interiors w),fC w ⟨inner w i (Fin.last ((m+1)*d)),hp⟩=(π^d) i.val):=by
    intro w
    rcases hprops w with ⟨hc,hd',hs1,hEmbed,hsupp,hinner,hmarker,hocc,hdr,hinj,hold,hreserved,hs2,ht,hT,hlen,hverts,hOrd,hMarked,hdis,hOldAvoid,hDirection,hOldDirected⟩
    have he:=actual_sum_buffered_endpoint_agreement (hF w) (data w) (m+1) d hc hd' hs1 (ext w) (inner w) hsupp hinner hdis π Subtype.val (ψ w)
      (by intro a j hj;simpa only [retainedAndRawIntervalRoot] using hmarker (.inl a) j hj) (fC w) (hC w)
    constructor
    · intro i hp
      simpa only [bufferedInitialEndpointInComplement] using he.1 i
    · intro i hp
      simpa only [bufferedEndpointInComplement] using he.2 i
  have hDR:∀w,Disjoint (Interiors w) (data w).remaining:=fun w=>(hprops w).2.2.2.2.2.2.2.2.1
  have hOld:∀w,Disjoint (((data w).oldDomain\Interiors w).image (ψ w))
      (Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w)):=
    fun w=>(hprops w).2.2.2.2.2.2.2.2.2.2.2.1
  have hAbsAll:∀w,Disjoint (AbsAll w) A:=by
    intro w
    by_cases hw:w∈H
    · simpa [AbsAll,hw] using hAbs w hw
    · simp [AbsAll,hw]
  have hFirst:=actual_retained_completion_inner_agreement_all_hub_targets π d (m+1) (by omega) (fun e=>raw (Sum.inr e)) t Jret F hF
    (fun w=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
    (fun w=>{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w})
    data inner ψ A H AbsAll (Kbad Pack) assignNew orient BB g Φ fC hCycle hDR hC hR
    (fun w=>(hEnds w).1) (fun w=>(hEnds w).2) hOld hAbsAll hBB hEndList hag hfree
  have hNoNew:=actual_all_hub_completion_no_new_spokes π d (m+1) (by omega) (fun e=>raw (Sum.inr e)) t Jret F
    (fun w=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
    (fun w=>{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w})
    data inner ψ A AbsAll (fun w=>(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))
    (fun w=>prescribedMatchingEndpoints (prescribedAssignedArcs (Kbad Pack) assignNew orient w))
    BB g Φ fC hCycle hDR hC hR (fun w=>(hEnds w).1) (fun w=>(hEnds w).2) hAbsAll hBB hag
  refine ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,⟨hcapacityAll,hglobalAll⟩,hcompletion,piecesNew,Φ,fC,?_⟩
  refine ⟨hgraphNew,hC,hR,hZ,hImage,hYavoid,hDirected,hHost,hPacked,hFirst,hNoNew,⟨assignNew,orient,BB,g,hMcap,hBB,hEndList,hag,hfree⟩,?_⟩
  refine ⟨?_,?_,hPackAvoid,?_,?_,?_⟩
  · convert hKcover using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  · convert hJavoid using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  · convert hEunion using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  · convert hLoss using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  · convert hReserve using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
