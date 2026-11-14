module

public import Oberwolfach.LongSelectedPreparedEncodedSplitLoad
public import Oberwolfach.LongPreparedEncodedSplitLoadAndChangeGraphs
public import Oberwolfach.LongCorrectedActiveColumnNoNewSpokes
public import Oberwolfach.LongSameSampleBalancedExactChangeGraphsLocal
public import Oberwolfach.LongDualVortexEncodedActiveAndDeeper
public import Oberwolfach.LongMatchingPhysicalCorrectionFields
public import Oberwolfach.LongMatchedFullSampleBalancedDualSplitLoad
public import Oberwolfach.LongReferenceResidualPhysicalClosenessOnRoots
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingAllHub
public import Oberwolfach.LongMatchedFullSampleBalancedDualWithRetainedSpokeControl
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingGlobal
public import Oberwolfach.LongMatchedFullSampleBalancedDualWithSpokeControl
public import Oberwolfach.LongReferenceResidualPhysicalCloseness
public import Oberwolfach.LongMatchedFullSampleBalancedDualWithFactorDataExact
public import Oberwolfach.LongMatchedFullSampleBalancedDualCorrection
public import Oberwolfach.FirstVortexClassPreparedFullPackingGlobal
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
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance protectedSelectedSplitControlFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) protectedSelectedSplitControlSix : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance protectedSelectedSplitControlArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_protected_selected_encoded_split_load_and_change_graphs
    (d e r:ℕ) (ρ₀ rho ζ δLoss εInner eta:ℝ)
    (hρ₀:0<ρ₀) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hbudget:ζ+δLoss<eta) (hsupply:rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ))):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (K D:ℕ) (G:SimpleGraph (Fin n)) (hreg:G.IsRegularOfDegree D) (hD:0<D) (hd:0<d)
    (hρlo:ρ₀ ≤ initialIndexDensity U D) (hDlo:(n:ℝ)/2≤D)
    (π:Equiv.Perm (Fin n)) (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ Dmatch alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (hI:∀v,π v∈I↔v∈I)
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
    (κ boundary loc a δsmall ζsmall ρsmall δspoke:ℝ) (hκ:0<κ) (hθ0pre:0≤θ)
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
    (hρreserve:0≤ρreserve) (hListMargin:βfinal+2*ρreserve≤βpre)
    (mm:ℕ) (β ξ:ℝ) (Vort:Vortex U G D β εQ mm)
    (hIeq:I=Vort.extendedVertices 1) (hHeq:H=Vort.extendedIndices 1)
    (hπ:∀i v,π v∈Vort.extendedVertices i↔v∈Vort.extendedVertices i) (hζξ:ζ≤ξ) (ξClass:ℝ)
    (Q:∀(D₀:MarkedReferenceDeletion G π d (fun x=>rawExpandedMarkedCollapse x (z.1 x))),
      Finset (Finset (Fin n)⊕(Fin n×U))→Prop)
    (hSelectedEvent:∃D₀:MarkedReferenceDeletion G π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)),
      ∃C:Finset (Finset (Fin n)⊕(Fin n×U)), Q D₀ C ∧
      markedResourceRimGraph C≤longSelectedPhysicalGraph G π d z.1 ∧
      (C.card:ℝ)≤ρreserve*n ∧ (∃S:SimpleGraph (Fin n),S≤G ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀v,((changed ((longPhysicalStateGraph G z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
      (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph G z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph C≤S ∧
      (∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d z.1).Adj x y→S.Adj x y) ∧
      ∃Mhost:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
        LongClassMatchingDeletionWitness ζ G π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S Mhost Del ∧
        FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad G S π D mm d (r+4) β εQ Vort F hF θ lamAssign eps δlocal δglobal (αAssign/2) b ρstep ξ ζ a γ weight w z.1
          (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) Jret)),
    ∃D₀:MarkedReferenceDeletion G π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)),
    ∃C:Finset (Finset (Fin n)⊕(Fin n×U)), Q D₀ C ∧
    ∃S:SimpleGraph (Fin n), ∃Mhost:Fin n→Fin n→ℕ, ∃Del:SimpleGraph (Fin n),
      S≤G ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀v,((changed ((longPhysicalStateGraph G z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
      (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph G z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph C≤S ∧
      (∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d z.1).Adj x y→S.Adj x y) ∧
      LongClassMatchingDeletionWitness ζ G π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S Mhost Del ∧
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad G S π D mm d (r+4) β εQ Vort F hF θ lamAssign eps δlocal δglobal (αAssign/2) b ρstep ξ ζ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) Jret ∧
    let t:=startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun x=>rawExpandedApproximateCollapse x (z.1 x)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let Tmix:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let Q:=longRawSurvivingResources G π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q Tmix (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true;
    ∀(X:Finset (Fin n)) (Z:Finset U),
    RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζsmall Jret→
    (∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>raw (Sum.inr e)) w I-
      (I.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ w g)-
        (∑j,longAssignedSpokeProbability F hF K (r+4) θ w j))|<(n:ℝ)^(3/4:ℝ))→
    (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>raw (Sum.inr e)) v Finset.univ-
      ∑w:U,(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ w g)-
        (∑j,longAssignedSpokeProbability F hF K (r+4) θ w j))|<(n:ℝ)^(3/4:ℝ))→
    (∀v,((rawIntervalBoundaryHubSet π d (fun e=>raw (Sum.inr e)) Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ))→
    0<K→θ≤1→∀ζRet capActive:ℝ,
    0<capActive→0<εQ→εQ≤1/4→0<mm→0≤ζRet→ζRet≤capActive/128→
    (2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a γ*n)≤capActive*(εQ*n)/128→
    (∀E:ℕ,(E:ℝ)≤(θ*εQ^2+lamAssign*εQ)*(n:ℝ)^2+24*d*n→
      2*(⌈4*(E:ℝ)/(((ρstep/4)/40000)*n)⌉₊:ℕ)≤capActive*(εQ*n)/128)→
    RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t I Finset.univ ζRet Jret→
    (∀w g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K (r+4) θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))→
    MarkedFixedTerminalAbsorber G π d (r+4) (fun e=>rawExpandedMarkedCollapse e (z.1 e))
      (retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false) C X Z→
    (∀w,IsExtendingList (fun x y=>rawSelectedPhysicalRelation G π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
      (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w\(I∪retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)) βpre)→
    (I.card:ℝ)≤εInner*n→C.card≤e→∀p₂ k₂ u:ℝ,
    (∀v,|((rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K (r+4) θ w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
    (∀j v,|((∑x,sampledColourOrientation G (fun x=>z.1 (Sum.inl x)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability (initialIndexDensity U D*(1/100:ℝ)/2) (initialIndexDensity U D*((1/100:ℝ)/((r+4:ℕ):ℝ))/2) p₂ k₂ u j/2*G.degree v|<(n:ℝ)^(3/5:ℝ))→
    0≤γ→0≤θ→u≤2*θ→
    (∀v,|((sampledColourDegree G (fun e=>(z.1 (Sum.inl e)).1) 4 v):ℝ)-u*(G.degree v:ℝ)|≤(n:ℝ)^(3/5:ℝ))→
    (∀v,((changed ((longPhysicalStateGraph G z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
    ∀(εBalance ζChange ζGlobal lossRow lossCol:ℝ),0≤ζGlobal→
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let Hraw:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false;
    MarkedRestrictedBalanceWithSpokes G π d (r+4) Finset.univ Finset.univ εBalance σ Hraw→
    RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζGlobal Jret→
    (∀v,((Finset.univ.filter (fun w=>¬(Hraw false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossRow)→
    (∀w,((Finset.univ.filter (fun v=>¬(Hraw false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossCol)→
    2*(lossRow+(δspoke*n+(Real.sqrt δspoke*n+1)))+
      (εBalance+2*(((2*θ+2*max a (4*γ)+2*ξClass)*n+2*(δsmall*n+(κ*n+1)))+(n:ℝ)^(3/5:ℝ)+ζ*n+2*(6*d+2:ℕ)+ζ*n+((1+2/rho)*eta*n+1)))≤ζChange*n→
    2*(lossCol+10*θ*n)+εBalance≤ζChange*n→
    ∃Mix:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
      (∀c∈Mix,∀c'∈Mix,c≠c'→Disjoint (restrictedResourceSet R (Function.Embedding.subtype (·∈Q)) c)
        (restrictedResourceSet R (Function.Embedding.subtype (·∈Q)) c')) ∧
      (∀i,((longRawIncidenceSet Q i\Mix.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈Q)))).card:ℝ)≤
        max (a*n) (γ*(longRawIncidenceSet Q i).card)) ∧
    ∃(Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))) (Spokes:U→Finset (Fin n)),
      let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈Tmix))) (Mix.map q)
      let Sel:=longSelectedPhysicalGraph G π d z.1
      let Req:=fun x y=>Mhost x y=1 ∧ markedPhysicalRim G π (3*d)
        (fun x=>markedExpandedPhysicalCollapse (z.1 (Sum.inl x))) true x (π.symm y)≠1
      let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
      let Kplus:=fun Pack:Finset (Sym2 (Fin n))=>longClassInnerRequiredRepair S Used Kbase I Pack
      let DelPlus:=Del⊔markedResourceRimGraph C
      let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E
      let P:=longEligibleResidualArc Mhost Small ⊥
      let T₁:=longDualInitialMarked G (fun x=>z.1 (Sum.inl x)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
      ∃T:Finset {x:(Fin n)×(Fin n) // P x},
      (∀v,((changed ((longSelectedPhysicalGraph G π d z.1).neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤
        ((2*θ+2*max a (4*γ)+2*ξClass)*n+2*(δsmall*n+(κ*n+1)))+(n:ℝ)^(3/5:ℝ)+ζ*n+2*(6*d+2:ℕ)) ∧
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
        (∀v,v∉I→((changed ((longSelectedPhysicalGraph G π d z.1).neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤
          (2*θ+2*max a (4*γ)+2*ξClass)*n+2*((boundary+2*(max a γ*n))+(αAssign/16)*n+(κ*n+1))+
            (n:ℝ)^(3/5:ℝ)+ζ*n+2*(6*d+2:ℕ)) ∧
        (∀v,v∉I→((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree v:ℝ)≤
          loc+((I.card:ℝ)*eta+loc)/rho+1) ∧
        (∀v,v∉I→((prescribedPhysicalUnion E).degree v:ℝ)≤
          2*((boundary+2*(max a γ*n))+(αAssign/16)*n+(κ*n+1))) ∧
        ∃Cimage:U→Finset (Fin n),
          (∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉Cimage w→v∈Spokes w\Y w) ∧
          (∀v,v∉I→((Finset.univ.filter (fun w=>v∈Cimage w)).card:ℝ)≤
            (boundary+2*(max a γ*n))+(αAssign/16)*n+(κ*n+1)) ∧
      ∃τ:RawMarkedOutcome (Fin n) U Bool Bool,
        (∀e,τ (Sum.inr e)=rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) ∧
        (∀e:Sym2 (Fin n),e.toFinset⊆Vort.extendedVertices 1→τ (Sum.inl e)=markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) ∧
        (let f:=markedVortexActiveVertexEmbedding Vort 1
         let g:=markedVortexNonDeeperHubToPhysical Vort 0
         let ρ:=markedVortexActivePermutation Vort π hπ 1;
         rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g τ)=
         rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g (fun e=>rawExpandedMarkedCollapse e (z.1 e)))) ∧
        (∀ (i:ℕ), 1 ≤ i →
          rawMarkedRestrictPair (markedVortexVertexEmbedding Vort i) (markedVortexHubEmbedding Vort i) (fun e=>rawExpandedMarkedCollapse e (z.1 e))=
          rawMarkedRestrictPair (markedVortexVertexEmbedding Vort i) (markedVortexHubEmbedding Vort i) τ ∧
          (fun b v u=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false b (markedVortexVertexEmbedding Vort i v) (markedVortexHubEmbedding Vort i u))=
          (fun b v u=>if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false true (markedVortexVertexEmbedding Vort i v) (markedVortexHubEmbedding Vort i u)
            else markedVortexVertexEmbedding Vort i v∈Spokes (markedVortexHubEmbedding Vort i u)\Y (markedVortexHubEmbedding Vort i u))) ∧
        (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
          if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
          else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y) ∧
        MarkedRemainderDivisible
          (fun e:MarkedSampleArc G π (3*d) (fun e=>τ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
          (fun e:MarkedSampleArc G π (3*d) (fun e=>τ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
          (retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false true true) Finset.univ
          (Finset.univ.filter (fun z:(Fin n)×U=>H₀ z.1 z.2∨retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false true true z.1 z.2)) (r+4) ∧
        ∃(FR:SimpleGraph (Fin n)) (FS:SimpleGraph (Fin n⊕U)),
          (∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset) ∧
          (∀v,(FR.degree v:ℝ)≤((2*θ+2*max a (4*γ)+2*ξClass)*n+2*(δsmall*n+(κ*n+1)))+(n:ℝ)^(3/5:ℝ)+ζ*n+2*(6*d+2:ℕ)+ζ*n+((1+2/rho)*eta*n+1)) ∧
          (∀v,v∉I→(FR.degree v:ℝ)≤
            (2*θ+2*max a (4*γ)+2*ξClass)*n+2*((boundary+2*(max a γ*n))+(αAssign/16)*n+(κ*n+1))+
              (n:ℝ)^(3/5:ℝ)+ζ*n+2*(6*d+2:ℕ)+ζ*n+(loc+((I.card:ℝ)*eta+loc)/rho+1)) ∧
          (∀b v w,¬(Hraw b v w↔(if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false true true v w else v∈Spokes w\Y w))→FS.Adj (Sum.inl v) (Sum.inr w)) ∧
          (∀x,(FS.degree x:ℝ)≤ζChange*n) ∧
          (∀B:Finset U,∀v,v∉I→(∑w∈B,if ¬(Hraw false v w↔v∈Spokes w\Y w) then (1:ℝ) else 0)≤
            2*(ζGlobal*n+((boundary+2*(max a γ*n))+(αAssign/16)*n+(κ*n+1)))+
              (εBalance+2*((2*θ+2*max a (4*γ)+2*ξClass)*n+2*((boundary+2*(max a γ*n))+(αAssign/16)*n+(κ*n+1))+
                (n:ℝ)^(3/5:ℝ)+ζ*n+2*(6*d+2:ℕ)+ζ*n+(loc+((I.card:ℝ)*eta+loc)/rho+1)))) ∧
        (let W:=↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))
         let Z:=markedVortexNonDeeperHubType Vort 0
         let f:=markedVortexActiveVertexEmbedding Vort 1
         let g:=markedVortexNonDeeperHubToPhysical Vort 0
         let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false
         let H':=fun b v w=>if b then H true v w else v∈Spokes w\Y w
         let HL:=fun b v u=>H b (f v) (g u)
         let HL':=fun b v u=>H' b (f v) (g u)
         let FS:=markedSpokeChangeGraph HL HL';
         (∀b v u,¬(HL b v u↔HL' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) ∧
         (∀u:Z,(FS.degree (Sum.inr u):ℝ)≤capActive*Fintype.card W)) ∧
        LongResidualSpokeCompletionControl π d raw t Jret Spokes θ δspoke :=by
  obtain ⟨N,hN⟩:=long_selected_prepared_encoded_split_load_and_change_graphs d e r ρ₀ rho ζ δLoss εInner eta hρ₀ hrho heta hetaR hbudget hsupply
  refine ⟨N,?_⟩
  intro n hn _ U _ _ K D G hreg hD hd hρlo hDlo π z I θ Dmatch alpha γ eps βList F hF weight w hI hU Jret hnoshort hd2 H absorber hAbs δlocal ρstep δglobal εQ lamAssign αAssign b βpre βfinal ρreserve hρstep hb hbsmall hαb hθδ hεδ hβ hβ1 hδ hδbound hn0 hnβ hnδ hu κ boundary loc a δsmall ζsmall ρsmall δspoke hκ hθ0pre hδsmall hθpos hθsmall hspacing hKsmall hθ1small hnsmall hζsmall hζsmall0 hρsmall hscale hbadsmall hδspoke hspokeScale hSharp hθκ hδstrong hnstrong hloc hboundary hlocGlobal hlocalBudget hρreserve hListMargin mm β ξ Vort hIeq hHeq hπ hζξ ξClass Q hSelectedEvent
  obtain ⟨D₀,C,hQ,hreserve,hCreserve,hSelected⟩:=hSelectedEvent
  refine ⟨D₀,C,hQ,?_⟩
  have hc:=hN n hn
  have hdec:selectedPreparedSplitControlFin n=protectedSelectedSplitControlFin n:=Subsingleton.elim _ _
  have hdecK:selectedPreparedSplitControlFin K=protectedSelectedSplitControlFin K:=Subsingleton.elim _ _
  have hdec6:selectedPreparedSplitControlSix=protectedSelectedSplitControlSix:=Subsingleton.elim _ _
  try rw [hdec] at hc
  try rw [hdecK] at hc
  try rw [hdec6] at hc
  exact hc U K D G hreg hD hd hρlo hDlo π z I θ Dmatch alpha γ eps βList F hF weight w D₀ C hI hreserve hU Jret hnoshort hd2 H absorber hAbs δlocal ρstep δglobal εQ lamAssign αAssign b βpre βfinal ρreserve hρstep hb hbsmall hαb hθδ hεδ hβ hβ1 hδ hδbound hn0 hnβ hnδ hu κ boundary loc a δsmall ζsmall ρsmall δspoke hκ hθ0pre hδsmall hθpos hθsmall hspacing hKsmall hθ1small hnsmall hζsmall hζsmall0 hρsmall hscale hbadsmall hδspoke hspokeScale hSharp hθκ hδstrong hnstrong hloc hboundary hlocGlobal hlocalBudget hρreserve hCreserve hListMargin mm β ξ Vort hIeq hHeq hπ hζξ ξClass hSelected
end Oberwolfach
