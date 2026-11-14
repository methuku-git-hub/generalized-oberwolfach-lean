module

public import Oberwolfach.LongMatchedSameBalancedDualSplitLoadWithPackingData
public import Oberwolfach.FirstVortexClassRetainedFullPackingHostAvoidReserveScale
public import Oberwolfach.LongClassWitnessRetainedDynamicSameBalancedScale
public import Oberwolfach.LongBalancedScalePrescribedFromMatching
public import Oberwolfach.LongMatchedHostBalancedDualWithRetainedSpokeControl
public import Oberwolfach.FirstVortexClassRetainedFullPackingHostAvoidReserveOriented
public import Oberwolfach.LongMatchedHostBalancedDualWithSpokeControl
public import Oberwolfach.FirstVortexClassFullPackingHostAvoidReserveOriented
public import Oberwolfach.LongMatchedHostBalancedDualWithFactorDataExact
public import Oberwolfach.FirstVortexClassFullPackingHostAvoidReserveExact
public import Oberwolfach.LongMatchedMinimumBalancedDualWithFactorData
public import Oberwolfach.LongMatchedClassFullPackingHostGeometry
public import Oberwolfach.FirstVortexClassFullPackingHostAvoidReserve
public import Oberwolfach.LongMatchedHostBalancedDualCorrection
public import Oberwolfach.LongClassWitnessDynamicSameBalancedResidual
public import Oberwolfach.LongMatchedSameBalancedDualCorrection
public import Oberwolfach.LongSameBalancedPhysicalResidual
public import Oberwolfach.LongSameSampleResidualDivisibility
public import Oberwolfach.LongWitnessClassRepairedInnerHostEncoding
public import Oberwolfach.LongMatchedRequiredPackingReady
public import Oberwolfach.LongMatchedClassDynamicHostCompletionReady
public import Oberwolfach.LongMatchedDualUsedEventual

@[expose] public section
/-! The corrected type partition and the completed old/prescribed packing
are obtained on one sample, with the same class orientation and matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchedFullSampleBalancedSplitFactorSpokeControlFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) matchedFullSampleBalancedSplitFactorSpokeControlSix : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance matchedFullSampleBalancedSplitFactorSpokeControlArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_matched_full_sample_balanced_dual_with_split_load_spoke_control
    (d e r:ℕ) (ρ₀ rho ζ δLoss εInner eta:ℝ)
    (hρ₀:0<ρ₀) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hbudget:ζ+δLoss<eta) (hsupply:rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ))):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (K D:ℕ) (G:SimpleGraph (Fin n)) (hreg:G.IsRegularOfDegree D) (hD:0<D) (hd:0<d)
    (hρlo:ρ₀ ≤ initialIndexDensity U D) (hDlo:(n:ℝ)/2≤D)
    (π:Equiv.Perm (Fin n)) (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ Dmatch alpha γ eps βList a:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness ζ G π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S Mhost Del)
    (hI:∀v,π v∈I↔v∈I)
    (hclass:∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d z.1).Adj x y→S.Adj x y)
    (hreserve:markedResourceRimGraph C≤longSelectedPhysicalGraph G π d z.1)
    (hU:0<Fintype.card U)
    (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun x=>rawExpandedApproximateCollapse (Sum.inr x) (z.1 (Sum.inr x))) false)
      (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hd2:2≤d)
    (H:Finset U) (absorber:U→Finset (Fin n)) (hAbs:∀w∈H,Disjoint (absorber w) I) (δlocal ρstep δglobal:ℝ)
    (εQ lamAssign αAssign b βpre βfinal ρreserve:ℝ)
    (hρstep:0<ρstep) (hb:0≤b) (hbsmall:b≤((ρstep/4)/40000)/16) (hαb:αAssign/16≤b)
    (hθδ:10*θ≤δglobal) (hεδ:εQ≤δglobal) (hβ:0<βfinal) (hβ1:βfinal≤1)
    (hδ:0<δglobal) (hδbound:δglobal≤(βfinal/100)^2)
    (hn0:0<n) (hnβ:100/βfinal≤(n:ℝ)) (hnδ:2/Real.sqrt δglobal≤(n:ℝ)) (hu:Fintype.card U≤n)
    (κ boundary loc δsmall ζsmall ρsmall δspoke:ℝ) (hκ:0<κ) (hθ0:0≤θ)
    (hδsmall:0<δsmall) (hθpos:0<θ) (hθsmall:10*θ≤δsmall) (hspacing:1/(d:ℝ)≤θ/1024)
    (hKsmall:0<K) (hθ1small:θ≤1)
    (hnsmall:Classical.choose (first_vortex_all_hub_small_load_from_tests δsmall θ d hδsmall hθpos hθsmall hspacing)≤n)
    (hζsmall:ζsmall≤θ/4096) (hζsmall0:0≤ζsmall) (hρsmall:ρsmall≤θ/4096)
    (hscale:max a γ*n≤ρsmall*n) (hbadsmall:(αAssign/16)*n≤δsmall*n/4)
    (hδspoke:0≤δspoke) (hspokeScale:δsmall+κ≤Real.sqrt δspoke)
    (hSharp:2*(δsmall*n+(κ*n+1))≤δLoss*n)
    (hθκ:10*θ≤κ*(βfinal/4)) (hδstrong:δglobal≤(βfinal/200)^2) (hnstrong:200/βfinal≤(n:ℝ))
    (hloc:0≤loc) (hboundary:∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) Finset.univ v).card:ℝ)≤boundary)
    (hlocGlobal:loc≤eta*n)
    (hlocalBudget:(n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ)+
      (ζ*n+2*((boundary+2*(max a γ*n))+(αAssign/16)*n+(κ*n+1))+(6*d+2:ℕ))≤loc)
    (hρreserve:0≤ρreserve) (hCreserve:(C.card:ℝ)≤ρreserve*n) (hListMargin:βfinal+2*ρreserve≤βpre),
    let t:=startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun x=>rawExpandedApproximateCollapse x (z.1 x)
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
      (fun x=>markedExpandedPhysicalCollapse (z.1 (Sum.inl x))) true x (π.symm y)≠1
    let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=fun Pack:Finset (Sym2 (Fin n))=>longClassInnerRequiredRepair S Used Kbase I Pack
    let DelPlus:=Del⊔markedResourceRimGraph C;
    RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζsmall Jret→
    (∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>raw (Sum.inr e)) w I-
      (I.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ w g)-
        (∑j,longAssignedSpokeProbability F hF K (r+4) θ w j))|<(n:ℝ)^(3/4:ℝ))→
    (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>raw (Sum.inr e)) v Finset.univ-
      ∑w:U,(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ w g)-
        (∑j,longAssignedSpokeProbability F hF K (r+4) θ w j))|<(n:ℝ)^(3/4:ℝ))→
    (∀v,((rawIntervalBoundaryHubSet π d (fun e=>raw (Sum.inr e)) Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ))→
    (∀w,IsExtendingList (fun x y=>rawSelectedPhysicalRelation G π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
      (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w\(I∪retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)) βpre)→
    LongSelectedRetainedSourceDynamicAllHubLoad hU F G π d (r+4) ℓ raw t Jret z.1 H I Kplus Used absorber δlocal
      (fun occupied Pack=>(FirstVortexClassPrescribedAssignmentNoMarkedBudget G S Del Used (Kplus Pack) I π d z.1 t Jret H αAssign b ρstep θ εQ lamAssign occupied Pack ∧ Pack=Used.edgeFinset) ∧
        ∀w,((innerRequiredTargets H I (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
          (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n)
      ρstep θ δglobal (Mix.map q)→
    (hK:0<K)→(hγ0:0≤γ)→(hθ0:0≤θ)→(hθ1:θ≤1)→
    (∀i,((longRawIncidenceSet Q i\Mix.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈Q)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet Q i).card))→
    (∀w g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K (r+4) θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))→
    ∀ζRet:ℝ,RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t I Finset.univ ζRet Jret→
    (I.card:ℝ)≤εInner*n→C.card≤e→∀p₂ k₂ u:ℝ,
    (∀v,|((rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K (r+4) θ w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
    (∀j v,|((∑x,sampledColourOrientation G (fun x=>z.1 (Sum.inl x)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability (initialIndexDensity U D*(1/100:ℝ)/2) (initialIndexDensity U D*((1/100:ℝ)/((r+4:ℕ):ℝ))/2) p₂ k₂ u j/2*G.degree v|<(n:ℝ)^(3/5:ℝ))→
    ∃(Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))) (Spokes:U→Finset (Fin n)),
      let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E
      let P:=longEligibleResidualArc Mhost Small ⊥
      let T₁:=longDualInitialMarked G (fun x=>z.1 (Sum.inl x)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
      ∃T:Finset {x:(Fin n)×(Fin n) // P x},
      Pack=Used.edgeFinset ∧ Pack⊆(longApproximatePhysicalGraph G π d z.1).edgeFinset ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δglobal*Fintype.card (Fin n)) ∧
      (∀x y,Small.Adj x y→¬(markedResourceRimGraph C).Adj x y) ∧
      (∀v,directedInCount P T v=d*startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) ∧
      (∀x∈T,longMarkedArcEligible π d x.val) ∧ (∀x,x∉T→longOrdinaryArcEligible π d x.val) ∧
      (∀x,x.val.1∈I→(x∈T↔x∈T₁)) ∧
      (∀x,Sum.inl ({x.val.1,x.val.2}:Finset (Fin n))∈C→(x∈T↔x∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree v:ℝ)≤(1+2/rho)*eta*n+1) ∧
      (∀mark a b,a∈I→b∈I→
        (markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (z.1 (Sum.inl x))) mark a b=1 ↔
          if mark then ∃e:residualMarkedArc P T,e.val.val.1=a∧π.symm e.val.val.2=b
          else ∃e:residualOrdinaryArc P T,e.val.val.1=a∧e.val.val.2=b)) ∧
      let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun x=>raw (Sum.inr x)) false t Jret w=>d) Subtype.val
      let H₀:=fun v w=>v∈Spokes w\Y w
      MarkedRemainderDivisible
        (fun x:residualOrdinaryArc P T=>x.val.val.1) (fun x=>x.val.val.2)
        (fun x:residualMarkedArc P T=>x.val.val.1) (fun x=>π.symm x.val.val.2)
        (retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t Jret false true true) Finset.univ
        (Finset.univ.filter (fun z:(Fin n)×U=>H₀ z.1 z.2∨retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t Jret false true true z.1 z.2)) (r+4) ∧
      ∃A:Finset (Fin n×Fin n),Small.edgeFinset=A.image (fun a=>s(a.1,a.2)) ∧
        (∀a∈A,Mhost a.1 a.2=1) ∧
        LongFactorComplementProvenance F S G π d (r+4) raw t Jret Pack E A Spokes ∧
        LongResidualSpokeCompletionControl π d raw t Jret Spokes θ δglobal ∧
        (∀w,((I.filter (fun v=>retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t Jret false false false v w ∧ v∉Spokes w\Y w)).card:ℝ)≤
          ζRet*I.card+(2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a γ*n)+2*(⌈4*((Kplus Pack).edgeFinset.card:ℝ)/(((ρstep/4)/40000)*n)⌉₊:ℕ)) ∧
        (∀w v,v∈I→v∈Spokes w\Y w → retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t Jret false false false v w) ∧
        (∃Old,(FirstVortexClassPrescribedAssignmentNoMarkedBudget G S DelPlus Used (Kplus Pack) I π d z.1 t Jret H αAssign b ρstep θ εQ lamAssign Old Pack ∧ Pack=Used.edgeFinset) ∧
          ∀w,((innerRequiredTargets H I (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
            (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber Old w).card:ℝ)≤(θ/1024)*n) ∧
        (∀w∈H,∀v∈I,v∈Spokes w\Y w↔retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w) ∧
        (∀v,v∉I→((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree v:ℝ)≤
          loc+((I.card:ℝ)*eta+loc)/rho+1) ∧
        (∀v,v∉I→((prescribedPhysicalUnion E).degree v:ℝ)≤
          2*((boundary+2*(max a γ*n))+(αAssign/16)*n+(κ*n+1))) ∧
        ∃Cimage:U→Finset (Fin n),
          (∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉Cimage w→v∈Spokes w\Y w) ∧
          (∀v,v∉I→((Finset.univ.filter (fun w=>v∈Cimage w)).card:ℝ)≤
            (boundary+2*(max a γ*n))+(αAssign/16)*n+(κ*n+1)) ∧
          (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤2*(δsmall*n+(κ*n+1))) ∧
          (∀v,((Finset.univ.filter (fun w=>v∈Cimage w)).card:ℝ)≤(δsmall+κ)*n+1) ∧
          (∀w,((Cimage w).card:ℝ)≤10*θ*n) ∧
          LongResidualSpokeCompletionControl π d raw t Jret Spokes θ δspoke :=by
  obtain ⟨N,hN⟩:=long_matched_same_balanced_dual_correction_with_split_load_control_and_extra d e r ρ₀ rho ζ δLoss εInner eta hρ₀ hrho heta hetaR hbudget hsupply
  refine ⟨N,?_⟩
  intro n hn _ U _ _ K D G hreg hD hd hρlo hDlo π z I θ Dmatch alpha γ eps βList a F hF weight w D₀ C S Del Mhost hw hI hclass hreserve hU Jret hnoshort hd2 H absorber hAbs δlocal ρstep δglobal εQ lamAssign αAssign b βpre βfinal ρreserve hρstep hb hbsmall hαb hθδ hεδ hβ hβ1 hδ hδbound hn0 hnβ hnδ hu κ boundary loc δsmall ζsmall ρsmall δspoke hκ hθ0pre hδsmall hθpos hθsmall hspacing hKsmall hθ1small hnsmall hζsmall hζsmall0 hρsmall hscale hbadsmall hδspoke hspokeScale hSharp hθκ hδstrong hnstrong hloc hboundary hlocGlobal hlocalBudget hρreserve hCreserve hListMargin t raw ℓ R Tmix Q q φ Mix Used Sel Req Kbase Kplus DelPlus hrowsGlobal hfixedCount hcolumnCount hboundaryRaw hext hsource hK hγ0 hθ0 hθ1 hinc hcounts ζRet hrows hcard hC p₂ k₂ u hstarts hdegrees
  have hgeom:=long_matched_class_full_packing_host_geometry ζ G π z I θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Mhost hw hreserve Mix
  let Extra:=fun occupied Pack=>(FirstVortexClassPrescribedAssignmentNoMarkedBudget G S DelPlus Used (Kplus Pack) I π d z.1 t Jret H αAssign b ρstep θ εQ lamAssign occupied Pack ∧ Pack=Used.edgeFinset) ∧
    ∀w,((innerRequiredTargets H I (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
      (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n
  have hcomp:=first_vortex_class_retained_full_packing_host_avoiding_reserve_scale G S Del π d (r+4) ℓ z.1 t Jret F hF H I Kplus Used absorber
    δlocal ρstep θ εQ lamAssign αAssign b βfinal δglobal hρstep hb hbsmall hαb hθδ hεδ hβ hβ1 hδ hδbound hn0 hnβ hnδ hu hU Finset.univ n κ hκ hθ0pre (by exact_mod_cast hn0) (by simpa only [Finset.card_univ] using (show (Fintype.card U:ℝ)≤n by exact_mod_cast hu)) hθκ hδstrong hnstrong C Mhost
    hgeom.1 hgeom.2.1 hgeom.2.2 βpre ρreserve hρreserve hCreserve hListMargin hext (Mix.map q) hsource
  have hbal0:=long_class_witness_retained_dynamic_same_balanced_residual_scale ζ G π z I θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Mhost hw hreserve hd2 hnoshort hU t Jret H absorber hAbs δlocal ρstep δglobal Extra Finset.univ n κ
  have hdecB:classWitnessRetainedDynamicSameBalancedScaleFin n=matchedFullSampleBalancedSplitFactorSpokeControlFin n:=Subsingleton.elim _ _
  have hdecBK:classWitnessRetainedDynamicSameBalancedScaleFin K=matchedFullSampleBalancedSplitFactorSpokeControlFin K:=Subsingleton.elim _ _
  try rw [hdecB] at hbal0
  try rw [hdecBK] at hbal0
  have hbal:=hbal0 Mix hcomp
  have hbudget0:=long_balanced_scale_prescribed_from_matching hn0 hK hU F hF G π d (r+4) (by omega) (by omega) ℓ raw t Jret z.1 H I S Kplus Used DelPlus (markedResourceRimGraph C) absorber δlocal Mhost (fun x y=>Mhost x y=1 ∧ ¬(markedResourceRimGraph C).Adj x y) Extra ρstep θ δglobal a γ Finset.univ n κ hθ0 hθ1 hγ0 hnoshort Del.edgeFinset hcounts
  have hdecC:balancedScalePrescribedFromMatchingFin n=matchedFullSampleBalancedSplitFactorSpokeControlFin n:=Subsingleton.elim _ _
  have hdecCK:balancedScalePrescribedFromMatchingFin K=matchedFullSampleBalancedSplitFactorSpokeControlFin K:=Subsingleton.elim _ _
  try rw [hdecC] at hbudget0
  try rw [hdecCK] at hbudget0
  have hbudget:=hbudget0 Mix hinc hbal
  have hN':=hN n hn
  have hdec:matchedSameBalancedIncSplitExtraSpokeControlFin n=matchedFullSampleBalancedSplitFactorSpokeControlFin n:=Subsingleton.elim _ _
  have hdecK:matchedSameBalancedIncSplitExtraSpokeControlFin K=matchedFullSampleBalancedSplitFactorSpokeControlFin K:=Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdecK] at hN'
  have hres:=hN' U K D G hreg hD hd hρlo hDlo π z I θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Mhost hw hI hclass hreserve hU t Jret hnoshort hd2 rfl H absorber δlocal ρstep δglobal (2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a γ*n) ζRet hrows Extra boundary a κ ((αAssign/16)*n) loc δsmall ζsmall ρsmall δspoke hδsmall hθpos hθ1small hθsmall hspacing hn0 hKsmall hnsmall hζsmall hζsmall0 hρsmall hscale hbadsmall hδspoke hspokeScale hSharp hloc hγ0 hu Mix hrowsGlobal hfixedCount hcolumnCount hboundaryRaw hinc hboundary
    (by intro occupied Pack hh v;exact hh.1.1.1 v) hlocGlobal hlocalBudget hbudget (fun _ _ h=>h.1.2) hcard hC p₂ k₂ u hstarts hdegrees
  simpa only [Fintype.card_fin,Extra] using hres
end Oberwolfach
