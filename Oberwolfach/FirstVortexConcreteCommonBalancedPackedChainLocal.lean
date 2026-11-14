module

public import Oberwolfach.FirstVortexConcreteCommonBalancedRobustMatchingLocal
public import Oberwolfach.MarkedVortexPhysicalSpokeLossBudget
public import Oberwolfach.LongSplitLoadRobustChangeBudget
public import Oberwolfach.MarkedVortexCorrectedCompleteFromMatchingFields
public import Oberwolfach.FirstVortexConcreteTerminalCommonBalancedMatchingLocal
public import Oberwolfach.LongProvenanceCorrectedReserved
public import Oberwolfach.LongSplitLoadRobustChangeBudget
public import Oberwolfach.LongCommonEventBalanceAndRetention
public import Oberwolfach.FirstVortexConcreteTerminalMatchingReadyLocal
public import Oberwolfach.FirstVortexConcreteTerminalMatchingTestedLocal
public import Oberwolfach.FirstVortexGlobalRetentionToLocal
public import Oberwolfach.FirstVortexRetentionShrinkAfterChoices
public import Oberwolfach.LongMatchingReservedListsFromWitness
public import Oberwolfach.FirstVortexConcreteTerminalMatchingSplitLocal
public import Oberwolfach.FirstVortexConcreteMatchingTests
public import Oberwolfach.FirstVortexConcreteTerminalSplitInput
public import Oberwolfach.LongTerminalProtectedSelectedEncodedSplitLoadLocal
public import Oberwolfach.LongTerminalProtectedSelectedEncodedSplitLoadLocal
public import Oberwolfach.FirstVortexConcreteProtectedSplitInput
public import Oberwolfach.FirstVortexConcreteProtectedPreparedClass
public import Oberwolfach.FirstVortexConcreteCorrectionProtectedReserve
public import Oberwolfach.FirstVortexConcretePreparedClass
public import Oberwolfach.FirstVortexCombinedEventValidDeletionCorrection
public import Oberwolfach.FirstVortexConcreteBoundaryEvent
public import Oberwolfach.FirstVortexCombinedSelectorSelectedClass
public import Oberwolfach.LongSelectedProtectedClassAllHubSameDeletion
public import Oberwolfach.FirstVortexCombinedSelectorBoundaryEvent
public import Oberwolfach.FirstVortexSelectorLocalRetentionChoice
public import Oberwolfach.FirstVortexSelectorClassCapBoundary
public import Oberwolfach.FirstVortexConcreteSelectorMatchingBoundary
public import Oberwolfach.FirstVortexSelectorActualMatchingRates
public import Oberwolfach.FirstVortexAllClassesSynchronizedBoundaryTests
public import Oberwolfach.FirstVortexAllClassesAllHubBoundaryTests
public import Oberwolfach.FirstVortexAllClassesEarlyAllHubBoundary
public import Oberwolfach.FirstVortexAllClassesEarlyAllHubPrecise
public import Oberwolfach.LongUnassignedDensityBounds
public import Oberwolfach.FirstVortexMatchingIncidenceMargin
public import Oberwolfach.FirstVortexPreparedAllHubFromCommonPrecise
public import Oberwolfach.MarkedResourceRimGraph
public import Oberwolfach.FirstVortexRetainedSingleLevelToGlobal
public import Oberwolfach.FirstVortexClassRetainedFullPackingEarlySingleLevel
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingOutcome
public import Oberwolfach.FirstVortexClassProtectedFullPackingFromRetainedTests
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingOutcome
public import Oberwolfach.FirstVortexClassPrepareEarlyMatching
public import Oberwolfach.LongEarlyMatchingUniformResidualInput
public import Oberwolfach.LongCapacityAutomaticMargins
public import Oberwolfach.LongFirstPrescribedAsymptotic
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingOutcome
public import Oberwolfach.FirstVortexClassSourceFromRetainedTests
public import Oberwolfach.FirstVortexPreparedOrientedOutcome
public import Oberwolfach.FirstVortexOrientedAutomaticCoefficients
public import Oberwolfach.FirstVortexPreparedOrientedOutcome
public import Oberwolfach.FirstVortexProtectedAutomaticCoefficients
public import Oberwolfach.FirstVortexPreparedOrientedOutcome

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance concreteMatchingPackedFinLocal (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) concreteMatchingPackedSixLocal : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance concreteMatchingPackedArcLocal {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem first_vortex_concrete_common_balanced_packed_chain_local
    (α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret:ℝ) (d K r:ℕ) (Δ rho δLoss εInner eta:ℝ) (e:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δold) (hδ1:δold≤1) (hθ:0<θ) (hepsPos:0<eps)
    (hρ₀:0<ρ₀) (hbmatch:0<bmatch) (hαb:(2*α)/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:ε≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δold) (hθlocal:θ≤δold/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δold*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:3≤K) (hm:7≤(r+4))
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ)
    (hρ₀hi:ρ₀≤1) (hδglobal:0<δglobal) (hθglobal:10*θ≤δglobal)
    (hprecise:ε≤((ρ₀/4)/40000)/8192)
    (ξCap:ℝ) (hξPartCap:ξPart≤ξCap)
    (hCap:∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
      ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
        (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ))
    (hlamθ:lam≤θ) (hdlarge:(r+4)+2≤d)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hbudget:Δ+δLoss<eta) (hsupply:rho+Δ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ))):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dv) (hDlo:(n:ℝ)/2≤Dv) (hDhi:(Dv:ℝ)≤2*n) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (hcut:(1/(((r+4):ℝ)+1))/(d:ℝ)≤θ)
    (hcutHost:5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hεα:ε≤α/1000) (hlamhi:lam≤α/128)
    (a γ ρ ξSeed ΔSeed:ℝ)
    (haEq:a=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2)))
    (hγEq:γ=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))))
    (hρEq:ρ=θ/4096) (hΔeps:Δ≤eps/8)
    (hξSeed:ξSeed≤ξ) (hΔSeed:Δ≤ΔSeed) (heps1:eps≤1)
    (hζ:ζret≤θ/4096) (hζ0:0≤ζret)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (ζselect:ℝ) (hζselect:ζselect≤ζret) (Inner:Finset (Fin n)) (βList:ℝ)
    (terr τerr:ℝ) (hτerr:0≤τerr)
,
    FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Vort θ ρ₀ BM BO F hF weight w
      a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z Inner →
    ∀(γLoss σLoss:ℝ) (size a₀ b₀ e₀ f₀ L Bpart:ℕ) (εAbs ζCorr ξCorr:ℝ),
    (hsize:2*mm≤size)→(hL:L+1=Vort.length)→
    (hπ:∀i v,π v∈Vort.extendedVertices i↔v∈Vort.extendedVertices i)→
    0≤ξCorr→6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*n)≤min (γLoss*n) (σLoss*n)→
    ε≤εAbs→e₀≤Bpart→
    LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξPart z
      (Vort.extendedVertices 1) (Vort.extendedIndices 1) K Bpart θ Dv a γ eps βList F hF weight w→
    (let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
     let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
     MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr σ H
        (Vort.extendedVertices 1) (Vort.extendedIndices 1))→
    (∀T:SimpleGraph (Fin n),(∀v,T.degree v≤Bpart)→
      ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
        (∀x y,((spanningRestriction (⊤:SimpleGraph (Fin n)) (Vort.extendedVertices 1))⊔T).Adj x y→
          (S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n))→
    ∀(αAssign ρreserve:ℝ), αAssign/2=α → (e₀:ℝ)≤ρreserve*n → e₀≤e →
    ∀(βfinal κ boundary loc δsmall ρsmall δspoke:ℝ),
    0<Fintype.card U → ε≤δglobal → 0<βfinal → βfinal≤1 →
    δglobal≤(βfinal/100)^2 → 0<n → 100/βfinal≤(n:ℝ) →
    2/Real.sqrt δglobal≤(n:ℝ) → Fintype.card U≤n →
    0<κ → (hδsmall:0<δsmall) → (hθsmall:10*θ≤δsmall) →
    Classical.choose (first_vortex_all_hub_small_load_from_tests δsmall θ d hδsmall hθ hθsmall hspacing)≤n →
    ρsmall≤θ/4096 →
    max a γ*n≤ρsmall*n → (αAssign/16)*n≤δsmall*n/4 →
    0≤δspoke → δsmall+κ≤Real.sqrt δspoke →
    2*(δsmall*n+(κ*n+1))≤δLoss*n → 10*θ≤κ*(βfinal/4) →
    δglobal≤(βfinal/200)^2 → 200/βfinal≤(n:ℝ) →
    0≤loc → 4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)≤boundary →
    loc≤eta*n →
    (n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ)+
      (Δ*n+2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1))+(6*d+2:ℕ))≤loc →
    0≤ρreserve → βfinal+2*ρreserve≤βList/2 → Δ≤ξ →
    ∀(h:ℕ),1≤h→∀(sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon:ℕ)
      (ρHost:ℝ),0<ρHost→ρHost*Dv=2*Fintype.card U→
    ∀(βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
      εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance:ℝ),0≤γRich→
    ∀(levelWeight:∀i,(Fin (r+4+1)→markedVortexVertexType Vort i)→ℝ),
    LongMatchingCommonEvent P π Dv mm β ε Vort hπ r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L h
      F hF θ ρHost βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
      εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀Event sstarEvent kstarEvent τLevelEvent levelWeight (markedExpandedActualSelected π d z)→
    ∀(κaux κref:ℝ),0<ηBalance→0<κaux→0≤κref→κref≤κaux→
      εRefEvent=κref/4→0≤εNbrEvent→εNbrEvent≤κaux→
      κaux≤ηBalance/(8*((((r+4):ℕ):ℝ)+1))→κaux≤ζret→
    ∀(εStable ζStable capStable:ℝ) (sizeStable aStable bStable eStable fStable:ℕ),
    0≤ζStable→
    MarkedRetainedRobustChangeEvent P π d r false false εStable ζStable capStable sizeStable aStable bStable eStable fStable (markedExpandedActualSelected π d z)→
    ∃D₀:MarkedReferenceDeletion P π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)),
    ∃C:Finset (Finset (Fin n)⊕(Fin n×U)), longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1) γLoss σLoss e₀ (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) D₀ C ∧
    ∃S:SimpleGraph (Fin n), ∃Mhost:Fin n→Fin n→ℕ, ∃Del:SimpleGraph (Fin n),
      S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n) ∧
      (∀x∈(Vort.extendedVertices 1),∀y∈(Vort.extendedVertices 1),S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph C≤S ∧
      (∀x∈(Vort.extendedVertices 1),∀y∈(Vort.extendedVertices 1),(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C S Mhost Del ∧
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal (αAssign/2) bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2 ∧
    let t:=startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun x=>rawExpandedApproximateCollapse x (z.1 x)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let Tmix:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let Q:=longRawSurvivingResources P π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q Tmix (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true;
    0<K→θ≤1→∀ζRet capActive:ℝ,
    0<capActive→0<ε→ε≤1/4→0<mm→0≤ζRet→ζRet≤capActive/128→ζret≤ζRet*ε/2→
    (2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a γ*n)≤capActive*(ε*n)/128→
    (∀E:ℕ,(E:ℝ)≤(θ*ε^2+lamAssign*ε)*(n:ℝ)^2+24*d*n→
      2*(⌈4*(E:ℝ)/(((ρ₀/4)/40000)*n)⌉₊:ℕ)≤capActive*(ε*n)/128)→
    ((Vort.extendedVertices 1).card:ℝ)≤εInner*n→∀p₂ k₂ u:ℝ,
    (∀v,|((rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K (r+4) θ w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
    (∀j v,|((∑x,sampledColourOrientation P (fun x=>z.1 (Sum.inl x)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability (initialIndexDensity U Dv*(1/100:ℝ)/2) (initialIndexDensity U Dv*((1/100:ℝ)/((r+4:ℕ):ℝ))/2) p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ))→
    0≤γ→0≤θ→u≤2*θ→
    (∀v,|((sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) 4 v):ℝ)-u*(P.degree v:ℝ)|≤(n:ℝ)^(3/5:ℝ))→
    ∀(ζChange:ℝ),0≤ζChange→ζChange≤capStable→
    capActive≤ζChange→∀(cLocal:ℝ),0≤cLocal→capActive≤cLocal→
    ((2*θ+2*max a (4*γ)+2*ξPart)*n+2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1))+
      (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+(loc+(((Vort.extendedVertices 1).card:ℝ)*eta+loc)/rho+1))≤cLocal*((markedVortexInnerVertices Vort 0).card:ℝ)→
    (2*(ζret*n+((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1)))+
      ((ηBalance*n)+2*((2*θ+2*max a (4*γ)+2*ξPart)*n+2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1))+
        (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+(loc+(((Vort.extendedVertices 1).card:ℝ)*eta+loc)/rho+1))))≤cLocal*((markedVortexInnerVertices Vort 0).card:ℝ)→
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let Hraw:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false false;
    2*((ζret*n)+(δspoke*n+(Real.sqrt δspoke*n+1)))+
      ((ηBalance*n)+2*(((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(δsmall*n+(κ*n+1)))+(n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+((1+2/rho)*eta*n+1)))≤ζChange*n→
    2*((ζret*n)+10*θ*n)+(ηBalance*n)≤ζChange*n→
    ∃Mix:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
      (∀c∈Mix,∀c'∈Mix,c≠c'→Disjoint (restrictedResourceSet R (Function.Embedding.subtype (·∈Q)) c)
        (restrictedResourceSet R (Function.Embedding.subtype (·∈Q)) c')) ∧
      (∀i,((longRawIncidenceSet Q i\Mix.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈Q)))).card:ℝ)≤
        max (a*n) (γ*(longRawIncidenceSet Q i).card)) ∧
    ∃(Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))) (Spokes:U→Finset (Fin n)),
      let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈Tmix))) (Mix.map q)
      let Sel:=longSelectedPhysicalGraph P π d z.1
      let Req:=fun x y=>Mhost x y=1 ∧ markedPhysicalRim P π (3*d)
        (fun x=>markedExpandedPhysicalCollapse (z.1 (Sum.inl x))) true x (π.symm y)≠1
      let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d (Vort.extendedVertices 1) Req (fun x y=>Used.Adj x y)
      let Kplus:=fun Pack:Finset (Sym2 (Fin n))=>longClassInnerRequiredRepair S Used Kbase (Vort.extendedVertices 1) Pack
      let DelPlus:=Del⊔markedResourceRimGraph C
      let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E
      let Peligible:=longEligibleResidualArc Mhost Small ⊥
      let T₁:=longDualInitialMarked P (fun x=>z.1 (Sum.inl x)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
      ∃T:Finset {x:(Fin n)×(Fin n) // Peligible x},
      (∀v,((changed ((longSelectedPhysicalGraph P π d z.1).neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤
        ((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(δsmall*n+(κ*n+1)))+(n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)) ∧
      Pack=Used.edgeFinset ∧ Pack⊆(longApproximatePhysicalGraph P π d z.1).edgeFinset ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δglobal*Fintype.card (Fin n)) ∧
      (∀x y,Small.Adj x y→¬(markedResourceRimGraph C).Adj x y) ∧
      (∀v,directedInCount Peligible T v=d*startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) ∧
      (∀x∈T,longMarkedArcEligible π d x.val) ∧ (∀x,x∉T→longOrdinaryArcEligible π d x.val) ∧
      (∀x,x.val.1∈(Vort.extendedVertices 1)→(x∈T↔x∈T₁)) ∧
      (∀x,Sum.inl ({x.val.1,x.val.2}:Finset (Fin n))∈C→(x∈T↔x∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges Peligible T T₁)).degree v:ℝ)≤(1+2/rho)*eta*n+1) ∧
      (∀mark a b,a∈(Vort.extendedVertices 1)→b∈(Vort.extendedVertices 1)→
        (markedPhysicalRim P π (3*d) (fun x=>markedExpandedPhysicalCollapse (z.1 (Sum.inl x))) mark a b=1 ↔
          if mark then ∃e:residualMarkedArc Peligible T,e.val.val.1=a∧π.symm e.val.val.2=b
          else ∃e:residualOrdinaryArc Peligible T,e.val.val.1=a∧e.val.val.2=b)) ∧
      let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun x=>raw (Sum.inr x)) false t z.2 w=>d) Subtype.val
      let H₀:=fun v w=>v∈Spokes w\Y w
      MarkedRemainderDivisible
        (fun x:residualOrdinaryArc Peligible T=>x.val.val.1) (fun x=>x.val.val.2)
        (fun x:residualMarkedArc Peligible T=>x.val.val.1) (fun x=>π.symm x.val.val.2)
        (retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t z.2 false true true) Finset.univ
        (Finset.univ.filter (fun pair:(Fin n)×U=>H₀ pair.1 pair.2∨retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t z.2 false true true pair.1 pair.2)) (r+4) ∧
      ∃A:Finset (Fin n×Fin n),Small.edgeFinset=A.image (fun a=>s(a.1,a.2)) ∧
        (∀a∈A,Mhost a.1 a.2=1) ∧
        LongFactorComplementProvenance F S P π d (r+4) raw t z.2 Pack E A Spokes ∧
        LongResidualSpokeCompletionControl π d raw t z.2 Spokes θ δglobal ∧
        (∀w,(((Vort.extendedVertices 1).filter (fun v=>retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t z.2 false false false v w ∧ v∉Spokes w\Y w)).card:ℝ)≤
          ζRet*(Vort.extendedVertices 1).card+(2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a γ*n)+2*(⌈4*((Kplus Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*n)⌉₊:ℕ)) ∧
        (∀w v,v∈(Vort.extendedVertices 1)→v∈Spokes w\Y w → retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t z.2 false false false v w) ∧
        (∃Old,(FirstVortexClassPrescribedAssignmentNoMarkedBudget P S DelPlus Used (Kplus Pack) (Vort.extendedVertices 1) π d z.1 t z.2 (Vort.extendedIndices 1) αAssign bmatch ρ₀ θ ε lamAssign Old Pack ∧ Pack=Used.edgeFinset) ∧
          ∀w,((innerRequiredTargets (Vort.extendedIndices 1) (Vort.extendedVertices 1) (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
            (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t z.2) (fun _=>∅) Old w).card:ℝ)≤(θ/1024)*n) ∧
        (∀w∈(Vort.extendedIndices 1),∀v∈(Vort.extendedVertices 1),v∈Spokes w\Y w↔retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false false false v w) ∧
        (∀v,v∉(Vort.extendedVertices 1)→((changed ((longSelectedPhysicalGraph P π d z.1).neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤
          (2*θ+2*max a (4*γ)+2*ξPart)*n+2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1))+
            (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)) ∧
        (∀v,v∉(Vort.extendedVertices 1)→((physicalEdgeGraph (changedDirectedPhysicalEdges Peligible T T₁)).degree v:ℝ)≤
          loc+(((Vort.extendedVertices 1).card:ℝ)*eta+loc)/rho+1) ∧
        (∀v,v∉(Vort.extendedVertices 1)→((prescribedPhysicalUnion E).degree v:ℝ)≤
          2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1))) ∧
        ∃Cimage:U→Finset (Fin n),
          (∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉Cimage w→v∈Spokes w\Y w) ∧
          (∀v,v∉(Vort.extendedVertices 1)→((Finset.univ.filter (fun w=>v∈Cimage w)).card:ℝ)≤
            (boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1)) ∧
      ∃τ:RawMarkedOutcome (Fin n) U Bool Bool,
        (∀e,τ (Sum.inr e)=rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) ∧
        (∀e:Sym2 (Fin n),e.toFinset⊆Vort.extendedVertices 1→τ (Sum.inl e)=markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) ∧
        (let f:=markedVortexActiveVertexEmbedding Vort 1
         let g:=markedVortexNonDeeperHubToPhysical Vort 0
         let ρ:=markedVortexActivePermutation Vort π hπ 1;
         rawMarkedPairRims (P.comap f) ρ d (rawMarkedRestrictPair f g τ)=
         rawMarkedPairRims (P.comap f) ρ d (rawMarkedRestrictPair f g (fun e=>rawExpandedMarkedCollapse e (z.1 e)))) ∧
        (∀ (i:ℕ), 1 ≤ i →
          rawMarkedRestrictPair (markedVortexVertexEmbedding Vort i) (markedVortexHubEmbedding Vort i) (fun e=>rawExpandedMarkedCollapse e (z.1 e))=
          rawMarkedRestrictPair (markedVortexVertexEmbedding Vort i) (markedVortexHubEmbedding Vort i) τ ∧
          (fun b v u=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false false b (markedVortexVertexEmbedding Vort i v) (markedVortexHubEmbedding Vort i u))=
          (fun b v u=>if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false false true (markedVortexVertexEmbedding Vort i v) (markedVortexHubEmbedding Vort i u)
            else markedVortexVertexEmbedding Vort i v∈Spokes (markedVortexHubEmbedding Vort i u)\Y (markedVortexHubEmbedding Vort i u))) ∧
        (∀mark x y,markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
          if mark then ∃e:residualMarkedArc Peligible T,e.val.val.1=x∧π.symm e.val.val.2=y
          else ∃e:residualOrdinaryArc Peligible T,e.val.val.1=x∧e.val.val.2=y) ∧
        MarkedRemainderDivisible
          (fun e:MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
          (fun e:MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
          (retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false true true) Finset.univ
          (Finset.univ.filter (fun pair:(Fin n)×U=>H₀ pair.1 pair.2∨retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false true true pair.1 pair.2)) (r+4) ∧
        ∃(FR:SimpleGraph (Fin n)) (FS:SimpleGraph (Fin n⊕U)),
          (∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset) ∧
          (∀v,(FR.degree v:ℝ)≤((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(δsmall*n+(κ*n+1)))+(n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+((1+2/rho)*eta*n+1)) ∧
          (∀v,v∉(Vort.extendedVertices 1)→(FR.degree v:ℝ)≤
            (2*θ+2*max a (4*γ)+2*ξPart)*n+2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1))+
              (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+(loc+(((Vort.extendedVertices 1).card:ℝ)*eta+loc)/rho+1)) ∧
          (∀b v w,¬(Hraw b v w↔(if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false true true v w else v∈Spokes w\Y w))→FS.Adj (Sum.inl v) (Sum.inr w)) ∧
          (∀x,(FS.degree x:ℝ)≤ζChange*n) ∧
          (∀B:Finset U,∀v,v∉(Vort.extendedVertices 1)→(∑w∈B,if ¬(Hraw false v w↔v∈Spokes w\Y w) then (1:ℝ) else 0)≤
            2*(ζret*n+((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1)))+
              ((ηBalance*n)+2*((2*θ+2*max a (4*γ)+2*ξPart)*n+2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1))+
                (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+(loc+(((Vort.extendedVertices 1).card:ℝ)*eta+loc)/rho+1)))) ∧
        (let W:=↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))
         let Z:=markedVortexNonDeeperHubType Vort 0
         let f:=markedVortexActiveVertexEmbedding Vort 1
         let g:=markedVortexNonDeeperHubToPhysical Vort 0
         let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false false
         let H':=fun b v w=>if b then H true v w else v∈Spokes w\Y w
         let HL:=fun b v u=>H b (f v) (g u)
         let HL':=fun b v u=>H' b (f v) (g u)
         let FS:=markedSpokeChangeGraph HL HL';
         (∀b v u,¬(HL b v u↔HL' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) ∧
         (∀u:Z,(FS.degree (Sum.inr u):ℝ)≤capActive*Fintype.card W)) ∧
        LongResidualSpokeCompletionControl π d raw t z.2 Spokes θ δspoke ∧
        let Hnew:Bool→Fin n→U→Prop:=fun b v w=>if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false true true v w else v∈Spokes w\Y w;
        (∀v w,¬(Hnew false v w∧Hnew true v w)) ∧
        (∀w v x,Hnew false v w→Hnew true x w→v≠π x) ∧
        MarkedReservedTerminalAbsorberProperty
          (fun e:MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
          (fun e:MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
          (Hnew false) (Hnew true) π (3*d) r sizeStable aStable bStable eStable fStable εStable
        ∧ (∀v,v∉Vort.extendedVertices 1→(FR.degree v:ℝ)≤cLocal*((markedVortexInnerVertices Vort 0).card:ℝ))
        ∧ (∀B:Finset U,∀v,v∉Vort.extendedVertices 1→
            (∑w∈B,if ¬(Hraw false v w↔Hnew false v w) then (1:ℝ) else 0)≤cLocal*((markedVortexInnerVertices Vort 0).card:ℝ))
        ∧ (∀w v,v∈Vort.extendedVertices 1→Hnew false v w→Hraw false v w)
        ∧ (∀w,(((Vort.extendedVertices 1).filter (fun v=>Hraw false v w ∧ ¬Hnew false v w)).card:ℝ)≤
            cLocal*((markedVortexInnerVertices Vort 0).card:ℝ))
        ∧ (∀e,rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))=τ (Sum.inr e))
        ∧ (∀e:Sym2 (Fin n),e.toFinset⊆Vort.extendedVertices 1→τ (Sum.inl e)=rawExpandedMarkedCollapse (Sum.inl e) (z.1 (Sum.inl e)))
        ∧ (∀v w,v∈Vort.extendedVertices 1→w∈Vort.extendedIndices 1→(Hraw false v w↔Hnew false v w))
        ∧ (∀v,(FR.degree v:ℝ)≤ζChange*n)
        ∧ (let W:=↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))
           let Z:=markedVortexNonDeeperHubType Vort 0
           let f:=markedVortexActiveVertexEmbedding Vort 1
           let g:=markedVortexNonDeeperHubToPhysical Vort 0
           let HL:=fun b v u=>Hraw b (f v) (g u)
           let HL':=fun b v u=>if b then Hraw true (f v) (g u) else Hnew false (f v) (g u)
           let FSactive:=markedSpokeChangeGraph HL HL';
           (∀b v u,¬(Hraw b (f v) (g u)↔Hnew b (f v) (g u))→FSactive.Adj (Sum.inl v) (Sum.inr u)) ∧
           (∀u:Z,(FSactive.degree (Sum.inr u):ℝ)≤ζChange*Fintype.card W))
        ∧ (let W:=↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))
           let Z:=markedVortexNonDeeperHubType Vort 0
           let f:=markedVortexActiveVertexEmbedding Vort 1
           let g:=markedVortexNonDeeperHubToPhysical Vort 0
           let HL:=fun b v u=>Hraw b (f v) (g u)
           let HL':=fun b v u=>if b then Hraw true (f v) (g u) else Hnew false (f v) (g u)
           let FSactive:=markedSpokeChangeGraph HL HL';
           MarkedVortexPhysicalCorrectionFields P Dv mm β ε Vort π d false false
             (markedExpandedActualSelected π d z) σ τ Hraw Hnew (fun v w=>v∈Spokes w\Y w)
             FR FS FSactive ζChange cLocal)
 :=by
  obtain ⟨N,hN⟩:=first_vortex_concrete_common_balanced_robust_matching_local α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
    hα hlam hε hδ hδ1 hθ hepsPos hρ₀ hbmatch hαb hbd hεsmall hθδ hθlocal hθhi hlamlocal hspacing hd hK hm heps hξ hξ0
    hρ₀hi hδglobal hθglobal hprecise ξCap hξPartCap hCap hlamθ hdlarge Nret hNret hrho heta hetaR hbudget hsupply
  refine ⟨N,?_⟩
  intro n hn _ U _ _ P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ ρ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z ζselect hζselect Inner βList terr τerr hτerr hEvent
  intro γLoss σLoss size a₀ b₀ e₀ f₀ L Bpart εAbs ζCorr ξCorr hsize hL hπ hξCorr hbudgetCorr heAbs heB hEvery hProtected hHost αAssign ρreserve hαAssign hReserveScale hee
  intro βfinal κ boundary loc δsmall ρsmall δspoke hU hεδ hβ hβ1 hδbound hn0 hnβ hnδ hu hκ hδsmall hθsmall hnsmall hρsmall hscale hbadsmall hδspoke hspokeScale hSharp hθκ hδstrong hnstrong hloc hboundaryRate hlocGlobal hlocalBudget hρreserve hListMargin hΔξ
  intro h hh sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon ρHost hρHost hsizeHost
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance hγRich levelWeight hCommon
    κaux κref hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hκauxRet
  intro εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable hstable
  have hc:=hN n hn
  have hd:concreteCommonRobustFinLocal n=concreteMatchingPackedFinLocal n:=Subsingleton.elim _ _
  have hdK:concreteCommonRobustFinLocal K=concreteMatchingPackedFinLocal K:=Subsingleton.elim _ _
  have hd6:concreteCommonRobustSixLocal=concreteMatchingPackedSixLocal:=Subsingleton.elim _ _
  try rw [hd] at hc
  try rw [hdK] at hc
  try rw [hd6] at hc
  obtain ⟨D₀,C,hTerminal,S,Mhost,Del,hSP,hregS,hEdit,hInner,hRes,hCover,hwitness,hPrepared,hOut⟩:=hc U P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ ρ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z ζselect hζselect Inner βList terr τerr hτerr hEvent
    γLoss σLoss size a₀ b₀ e₀ f₀ L Bpart εAbs ζCorr ξCorr hsize hL hπ hξCorr hbudgetCorr heAbs heB hEvery hProtected hHost αAssign ρreserve hαAssign hReserveScale hee
    βfinal κ boundary loc δsmall ρsmall δspoke hU hεδ hβ hβ1 hδbound hn0 hnβ hnδ hu hκ hδsmall hθsmall hnsmall hρsmall hscale hbadsmall hδspoke hspokeScale hSharp hθκ hδstrong hnstrong hloc hboundaryRate hlocGlobal hlocalBudget hρreserve hListMargin hΔξ
    h hh sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon ρHost hρHost hsizeHost βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance hγRich levelWeight hCommon κaux κref hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hκauxRet εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable hstable
  refine ⟨D₀,C,hTerminal,S,Mhost,Del,hSP,hregS,hEdit,hInner,hRes,hCover,hwitness,hPrepared,?_⟩
  intro t raw ℓ R Tmix Q q φ hKpos hθone ζRet capActive hcap hεpos hεone hmmpos hζRet hζCap hretScale hPbound hEdgeBudget hcard p₂ k₂ u hstarts hdegrees hγ0 hθ0 huDensity hcolour ζChange hChange hChangeCap hCapChange cLocal hcLocal hCapLocal hRlocalBudget hSlocalBudget σ Hraw hBudgetRow hBudgetCol
  obtain ⟨Mix,hdis,hinc,Pack,E,Spokes,T,hclose,hPack,hApprox,hNew,hSafe,hCount,hMark,hOrd,hInnerT,hReserveT,hType,hAgree,hDiv,A,hSmall,hA,hFactor,hSpoke,hLoss,hNoNew,hExtra,hFirst,hcloseLocal,hTypeLocal,hNewLocal,Cimage,hProtect,hImageLocal,τtarget,hτint,hτinner,hτactive,hτdeep,hτcode,hτdiv,FR,FS,hFRims,hFR,hFRlocal,hFSchange,hFS,hFSlocal,hactive,hSpokeSmall,hTypes,hSep,hAbs⟩:=
    hOut hKpos hθone ζRet capActive hcap hεpos hεone hmmpos hζRet hζCap hretScale hPbound hEdgeBudget hcard p₂ k₂ u hstarts hdegrees hγ0 hθ0 huDensity hcolour ζChange hChange hChangeCap hBudgetRow hBudgetCol
  have hRlocal:∀v,v∉Vort.extendedVertices 1→(FR.degree v:ℝ)≤cLocal*((markedVortexInnerVertices Vort 0).card:ℝ):=by
    intro v hv;exact (hFRlocal v hv).trans hRlocalBudget
  have hSlocal:∀B:Finset U,∀v,v∉Vort.extendedVertices 1→
      (∑w∈B,if ¬(Hraw false v w↔v∈Spokes w\(fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t z.2 w=>d) Subtype.val) w) then (1:ℝ) else 0)≤cLocal*((markedVortexInnerVertices Vort 0).card:ℝ):=by
    intro B v hv;exact (hFSlocal B v hv).trans hSlocalBudget
  obtain ⟨Old,⟨hAssign,hPackOld⟩,hTarget⟩:=hExtra
  have hEdge:=hAssign.2.1
  have hLsmall:=hEdgeBudget _ hEdge
  let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t z.2 w=>d) Subtype.val
  let Hnew:Bool→Fin n→U→Prop:=fun b v w=>if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false true true v w else v∈Spokes w\Y w
  have hLossCap:=marked_vortex_physical_spoke_loss_budget P Dv mm β ε Vort hεpos hmmpos Hraw Hnew capActive ζRet
    (2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a γ*n)
    (⌈4*((longClassInnerRequiredRepair S (physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈Tmix))) (Mix.map q))
      (longRequiredPhysicalGraph S (S\(physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈Tmix))) (Mix.map q))) (longSelectedPhysicalGraph P π d z.1) π d (Vort.extendedVertices 1)
        (fun x y=>Mhost x y=1 ∧ markedPhysicalRim P π (3*d) (fun x=>markedExpandedPhysicalCollapse (z.1 (Sum.inl x))) true x (π.symm y)≠1)
        (fun x y=>(physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈Tmix))) (Mix.map q)).Adj x y))
      (Vort.extendedVertices 1) Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*n)⌉₊:ℕ) hcap.le hζCap (by simpa only [Fintype.card_fin] using hPbound) (by simpa only [Fintype.card_fin] using hLsmall) (by
      intro w
      have hh:=hLoss w
      dsimp only [Hnew,Y,Hraw,raw,t,rawExpandedApproximateCollapse,id,Bool.false_eq_true,if_false] at hh ⊢
      convert hh using 1 <;> congr! 12 <;> first | rfl | exact Subsingleton.elim _ _)
  have hLossLocal:∀w,(((Vort.extendedVertices 1).filter (fun v=>Hraw false v w ∧ ¬Hnew false v w)).card:ℝ)≤cLocal*((markedVortexInnerVertices Vort 0).card:ℝ):=by
    intro w
    have hh:=(hLossCap w).trans (mul_le_mul_of_nonneg_right hCapLocal (Nat.cast_nonneg _))
    convert hh using 1 <;> congr! 12 <;> first | rfl | exact Subsingleton.elim _ _
  have hSloc':∀B:Finset U,∀v,v∉Vort.extendedVertices 1→
      (∑w∈B,if ¬(Hraw false v w↔Hnew false v w) then (1:ℝ) else 0)≤cLocal*((markedVortexInnerVertices Vort 0).card:ℝ):=by
    intro B v hv
    have hh:=hSlocal B v hv
    dsimp only [Hnew,Y,Bool.false_eq_true,if_false] at hh ⊢
    convert hh using 1 <;> congr! 12 <;> first | rfl | exact Subsingleton.elim _ _
  have hNoNew':∀w v,v∈Vort.extendedVertices 1→Hnew false v w→Hraw false v w:=by
    intro w v hv hnew
    apply hNoNew w v hv
    simpa only [Hnew,Y,Bool.false_eq_true,if_false] using hnew
  have hRate:=long_split_load_robust_change_budget n ζret δspoke ηBalance
    (((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(δsmall*n+(κ*n+1)))+(n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+((1+2/rho)*eta*n+1))
    ζChange ζChange hζ0 hδspoke hηBalance.le hChange le_rfl hBudgetRow
  have hFRglobal:∀v,(FR.degree v:ℝ)≤ζChange*n:=fun v=>(hFR v).trans hRate
  have hInterval:∀e,rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))=τtarget (Sum.inr e):=fun e=>(hτint e).symm
  have hRawInner:∀e:Sym2 (Fin n),e.toFinset⊆Vort.extendedVertices 1→τtarget (Sum.inl e)=rawExpandedMarkedCollapse (Sum.inl e) (z.1 (Sum.inl e)):=by
    intro e he
    simpa only [rawExpandedMarkedCollapse] using hτinner e he
  have hOrdinary:∀v w,v∈Vort.extendedVertices 1→w∈Vort.extendedIndices 1→(Hraw false v w↔Hnew false v w):=by
    intro v w hv hw
    have hh:=(hFirst w hw v hv).symm
    simpa only [Hraw,Hnew,Y,raw,t,rawExpandedApproximateCollapse,id,Bool.false_eq_true,if_false] using hh
  have hActiveChange:=hactive.1
  have hActiveDegree:=hactive.2
  have hActiveBound:=mul_le_mul_of_nonneg_right hCapChange (Nat.cast_nonneg (Fintype.card ↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))))
  have hMarkedEq:retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false true true =
      retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false true:=by
    funext v w
    apply propext
    exact retained_marked_spokes_independent_of_ordinary_colour π d (fun e=>z.1 (Sum.inr e)) false false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 true false v w
  have hActive:let W:=↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))
      let Z:=markedVortexNonDeeperHubType Vort 0
      let f:=markedVortexActiveVertexEmbedding Vort 1
      let g:=markedVortexNonDeeperHubToPhysical Vort 0
      let HL:=fun b v u=>Hraw b (f v) (g u)
      let HL':=fun b v u=>if b then Hraw true (f v) (g u) else Hnew false (f v) (g u)
      let FSactive:=markedSpokeChangeGraph HL HL';
      (∀b v u,¬(Hraw b (f v) (g u)↔Hnew b (f v) (g u))→FSactive.Adj (Sum.inl v) (Sum.inr u)) ∧
      (∀u:Z,(FSactive.degree (Sum.inr u):ℝ)≤ζChange*Fintype.card W):=by
    refine ⟨?_,?_⟩
    · intro b v w hdiff
      apply hActiveChange b v w
      cases b with
      | false =>
          simpa only [Hraw,Hnew,Y,raw,t,rawExpandedApproximateCollapse,id,Bool.false_eq_true,if_false] using hdiff
      | true =>
          exfalso
          apply hdiff
          dsimp only [Hraw,Hnew,Y,raw,t,rawExpandedApproximateCollapse,id,Bool.true_eq_false,if_true]
          rw [hMarkedEq]
          simp only [if_true]
    · intro w
      have hh:=(hActiveDegree w).trans hActiveBound
      dsimp only [Hraw,Hnew,Y,raw,t,rawExpandedApproximateCollapse,id,Bool.false_eq_true,if_false] at hh ⊢
      convert hh using 1 <;> congr! 12 <;> first | rfl | exact Subsingleton.elim _ _
  have hNewEq:Hnew=(fun b v w=>if b then Hraw true v w else v∈Spokes w\Y w):=by
    funext b v w
    apply propext
    cases b with
    | false => simp only [Hnew,Y,Bool.false_eq_true,if_false]
    | true =>
        dsimp only [Hnew,Hraw,Y,raw,t,rawExpandedApproximateCollapse,id,Bool.true_eq_false,if_true]
        rw [hMarkedEq]
  have hPacked:let W:=↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))
      let Z:=markedVortexNonDeeperHubType Vort 0
      let f:=markedVortexActiveVertexEmbedding Vort 1
      let g:=markedVortexNonDeeperHubToPhysical Vort 0
      let HL:=fun b v u=>Hraw b (f v) (g u)
      let HL':=fun b v u=>if b then Hraw true (f v) (g u) else Hnew false (f v) (g u)
      let FSactive:=markedSpokeChangeGraph HL HL';
      MarkedVortexPhysicalCorrectionFields P Dv mm β ε Vort π d false false
        (markedExpandedActualSelected π d z) σ τtarget Hraw Hnew (fun v w=>v∈Spokes w\Y w) FR FS FSactive ζChange cLocal:=by
    refine ⟨hTypes,hSep,hInterval,hFRims,hFSchange,?_,?_,hNewEq,hRawInner,hOrdinary,?_,?_,hRlocal,?_,hNoNew',?_⟩
    · simpa only [Fintype.card_fin] using hFRglobal
    · simpa only [Fintype.card_fin] using hFS
    · simpa only [markedExpandedActualSelected,Hraw,raw,t,rawExpandedApproximateCollapse,rawExpandedMarkedCollapse,id] using hActive.1
    · exact hActive.2
    · intro B v hv
      have hh:=hSloc' B v hv
      convert hh using 1 <;> congr! 12 <;> first | rfl | exact Subsingleton.elim _ _
    · intro w
      have hh:=hLossLocal w
      convert hh using 1 <;> congr! 12 <;> first | rfl | exact Subsingleton.elim _ _
  exact ⟨Mix,hdis,hinc,Pack,E,Spokes,T,hclose,hPack,hApprox,hNew,hSafe,hCount,hMark,hOrd,hInnerT,hReserveT,hType,hAgree,hDiv,A,hSmall,hA,hFactor,hSpoke,hLoss,hNoNew,⟨Old,⟨hAssign,hPackOld⟩,hTarget⟩,hFirst,hcloseLocal,hTypeLocal,hNewLocal,Cimage,hProtect,hImageLocal,τtarget,hτint,hτinner,hτactive,hτdeep,hτcode,hτdiv,FR,FS,hFRims,hFR,hFRlocal,hFSchange,hFS,hFSlocal,hactive,hSpokeSmall,hTypes,hSep,hAbs,hRlocal,hSloc',hNoNew',hLossLocal,hInterval,hRawInner,hOrdinary,hFRglobal,hActive,hPacked⟩
end Oberwolfach
