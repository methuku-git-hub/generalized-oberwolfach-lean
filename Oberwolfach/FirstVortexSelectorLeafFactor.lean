module

public import Oberwolfach.FirstVortexConcreteAllWeightsSampleFactor
public import Oberwolfach.FirstVortexConcreteConstructedSampleFactor
public import Oberwolfach.FirstVortexConcreteConstructedWeightsFactor
public import Oberwolfach.FirstVortexConcreteFactorSelection
public import Oberwolfach.LongMatchingReconstructionFromSameSample
public import Oberwolfach.FirstVortexGeometricChainInputs
public import Oberwolfach.FirstVortexDensityParentLowerCard
public import Oberwolfach.FirstVortexSelectedParentProbabilities
public import Oberwolfach.FirstVortexExactParentCapBound
public import Oberwolfach.FirstVortexSelectedParentChainRates
public import Oberwolfach.LongAssignedSamplingRecipe

@[expose] public section
/-! Specialize the level-chain continuation to the actual parent event,
weights and sampling probabilities selected by the original hierarchy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance selectorLeafFactorFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) selectorLeafFactorSix:DecidableEq (Fin 6):=instDecidableEqFin 6
local instance selectorLeafFactorArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem first_vortex_selector_leaf_factor
    {n K Dclass:ℕ} [Nonempty (Fin n)] (hEven:Even Dclass)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex (Fin (Dclass/2)) P Dv β ε mm)
    (hπ:∀i v,π v∈Vort.extendedVertices i↔v∈Vort.extendedVertices i)
    (active εStable:ℝ) (eStable:ℕ)
    (F:(Fin (Dclass/2))→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ:ℝ)
    (k₀ NI Kgeom aParent bParent eParent:ℕ)
    (NGeom:ℕ→ℕ) (hNGeom:∀j,1≤j→1≤NGeom j)
    (αRef ρ₀ δSelected εSelected ζSelected εAbsP ζAbsP βconfigP βCommonP εRef:ℝ)
    (βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut:ℝ)
    (hα:0<αRef) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity (Fin (Dclass/2)) Dv)
    (hκ:0<κ) (hx:0<x) (hθDeep:0<thetaDeep) (heta:0<eta) (hd:2≤d) (hε:0<ε)
    (hxi0:0≤xiDeep)
    (hXiScale:(4*(Kgeom:ℝ)+((3*r+50:ℕ):ℝ))*xiDeep≤κ/2)
    (hTstar:1/(200*((r+4:ℕ):ℝ))≤(1/100)/(((r+4):ℕ):ℝ))
    (hDeepSource:∀ρ t:ℝ,ρ₀≤ρ→1/(200*((r+4:ℕ):ℝ))≤t→(1+2/ρ)*xiDeep≤t*ω/32)
    (δbase ζFixed ζCut cap₁ cap₂:ℝ)
    (hAt:FirstVortexActualParentAlignedAt r ρ₀ (1/100) (1/(200*((r+4:ℕ):ℝ)))
      (successorWeightUpper k₀ ((2*αRef)/4)) δbase ζFixed κ x thetaDeep eta ε etaBal cap₁ cap₂ βA
      (markedLocalCycleCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ))))
      (markedLocalPathCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ)))) δSelected εSelected ζSelected)
    (hβA:βA≤βCommonP) (hrec:βrec≤βA) (hεRef:εRef≤(κ/2)/4)
    (hβ:β≤1/4) (hIcut0:0≤hIcut) (hEtaBal:0<etaBal)
    (hδAlpha:deltaI≤αRef/32) (hδStar:deltaI≤(ρ₀/(800*((r+4:ℕ):ℝ)))/32)
    (hδTime:2*deltaI≤(1/(200*((r+4:ℕ):ℝ)))/8)
    (hIStar:2*hIcut≤αRef*(ρ₀/(800*((r+4:ℕ):ℝ)))/4)
    (hδbaseCut:δbase≤ζCut) (hCut:2*hIcut≤(1/(200*((r+4:ℕ):ℝ)))/8-ζCut)
    (hn:0<n) (hU:Fintype.card (Fin (Dclass/2))≤n) (hDpos:0<Dv) (hDlo:(n:ℝ)/2≤Dv)
    (hρhi:initialIndexDensity (Fin (Dclass/2)) Dv≤1) (hζFixed:0<ζFixed)
    (hCycleFixed:3*βA≤markedLocalCycleCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ)))-(r+5:ℕ)*ζFixed)
    (hPathFixed:3*βA≤markedLocalPathCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ)))-(r+4:ℕ)*ζFixed)
    (hβrecT:βrec≤(1/(200*((r+4:ℕ):ℝ)))/4)
    (hActiveCap:active≤Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r (2*αRef)
      (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) ζFixed eta
      (successorWeightUpper k₀ ((2*αRef)/4)) (ρ₀/(800*((r+4:ℕ):ℝ))) hζFixed heta
      (successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2.le (by positivity) (by positivity)))
    (hdReconstruct:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (aMatch γMatch epsMatch Δ βList:ℝ)
    (lamAssign δlocal δglobal αSelected bmatch ξPrepared:ℝ)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (aCommon bCommon eCommon aRob bRob eRob fCommon hNbr:ℕ)
    (βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent ζEvent
      εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent τLevelEvent:ℝ)
    (hK:0<K) (hθ:0≤θ) (hθ1:θ≤1) (hγMatch:0≤γMatch) (hε1:ε≤1/4) (hmm:0<mm)
    (t c ζret ζlocal ηBalance κaux cap capStable:ℝ)
    (hret:FirstVortexRetentionBalanceRates r d ε active θ t c ζret ζlocal ηBalance κaux)
    (hactive:0<active) (hcap:0<cap) (hcapStable:cap≤capStable)
    (hactiveGlobal:active≤(min cap (1:ℝ))/2) (hactiveLocal:active≤(markedExplicitJointLocalCap (r+4) (r+12) etaBal x))
    (hChosen:FirstVortexExactParentCapBound r αRef ρ₀ κ ζFixed thetaDeep (successorWeightUpper k₀ ((2*αRef)/4)) cap hα hρ₀)
    (ξClass γLoss σLoss rhoMatch etaMatch κPack:ℝ) (hεHost:ε≤(2*αRef)/100000)
    (γLevel σLevel:ℝ) (hγ:0<γLevel) (hσ:0<σLevel)
    (γCore σCore extra:ℝ) (hγSplit:γCore+extra=γLevel) (hσSplit:σCore+extra=σLevel)
    (Nhost:ℕ) (hBudgetHost:Classical.choose (marked_vortex_terminal_budget eStable γLevel σLevel hγ hσ)≤Nhost)
    (hnHost:Nhost≤n)
    (hBundle:∃(weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Vort i)→ℝ)
      (weightActive:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Vort i):Finset (markedVortexVertexType Vort i)))→ℝ)
      (levelWeight:∀i,(Fin (r+4+1)→markedVortexVertexType Vort i)→ℝ)
      (z:MarkedExpandedActualOutcome (U:=Fin (Dclass/2)) π d),
    let chain_k₀:=k₀
    let chain_α:=αRef
    let chain_ρ₀:=ρ₀
    let chain_sstar:=(1/100:ℝ)
    let chain_tstar:=(1/(200*((r+4:ℕ):ℝ)))
    let chain_kstar:=(ρ₀/(800*((r+4:ℕ):ℝ)))
    let chain_εAbs:=εAbsP
    let chain_ζAbs:=ζAbsP
    let chain_βconfig:=βconfigP
    let chain_βCommon:=βCommonP
    let chain_εref:=εRef
    let chain_δref:=κ/2
    let chain_tolRef:=δSelected
    let chain_ζActive:=δSelected
    let chain_τ:=δSelected
    let chain_tolLocal:=δSelected
    let chain_ζLocal:=δSelected
    let chain_τParent:=δSelected
    let chain_tolParent:=δSelected
    let chain_ζParent:=δSelected
    let chain_epsBal:=εSelected
    let chain_ζBal:=ζSelected
    let chain_ζCut:=δSelected
    let chain_ζCfg:=δSelected
    let chain_rowErr:=δSelected
    let chain_ζCommon:=δSelected
    let chain_ζWide:=δSelected
    let chain_ζRow:=δSelected
    let chain_size:=(2*mm)
    let chain_a₀:=aParent
    let chain_b₀:=bParent
    let chain_e₀:=eParent
    let chain_f₀:=fCommon
    let chain_s₀:=(1/100:ℝ)
    let chain_p:=(initialIndexDensity (Fin (Dclass/2)) Dv*(1/100:ℝ)/2)
    let chain_kval:=(initialIndexDensity (Fin (Dclass/2)) Dv*(1/100:ℝ)/2/((r+4:ℕ):ℝ))
    let chain_q:=(longAssignedIntervalProbability F hF K (r+4) θ)
    let chain_s:=(longAssignedSpokeProbability F hF K (r+4) θ)
    let chain_weightParent:=weightParent
    let chain_weight:=weightActive
    let chain_βA:=βA
    let chain_βrec:=βrec
    let chain_κ:=κ
    let chain_ξ:=ξ
    let chain_thetaDeep:=thetaDeep
    let chain_ω:=ω
    let chain_xiDeep:=xiDeep
    let chain_etaBal:=etaBal
    let chain_x:=x
    let chain_eta:=eta
    let chain_deltaI:=deltaI
    let chain_hIcut:=hIcut
    let chain_αParent:=2*αRef
    let chain_κold:=κ/2
    let chain_xold:=x/2
    let chain_thetaOld:=thetaDeep/2
    let chain_etaOld:=eta/2
    let chain_N:=(NGeom d)
    let chain_NI:=NI
    let chain_Kgeom:=Kgeom
    let Common:=fun (outcome:RawMarkedRetainedOutcome (U:=Fin (Dclass/2)) (Color:=Bool) π d false)=>
      LongMatchingCommonEvent P π Dv mm β ε Vort hπ r K d (2*mm) aCommon bCommon eCommon aRob bRob eRob fCommon (Vort.length-1) hNbr
      F hF θ (initialIndexDensity (Fin (Dclass/2)) Dv) βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent (κ/2) (min αRef (1/2:ℝ)/2) (1/(200*((r+4:ℕ):ℝ))) ζEvent
      εSelected ζSelected εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀ (1/100:ℝ) (ρ₀/(800*((r+4:ℕ):ℝ))) τLevelEvent levelWeight outcome
    let Parent:=fun (outcome:RawMarkedRetainedOutcome (U:=Fin (Dclass/2)) (Color:=Bool) π d false)=>
      MarkedVortexParentRecordSmallerReferenceEvent r (r+12) chain_k₀ d chain_αParent chain_ρ₀ chain_sstar chain_tstar chain_kstar
      chain_εAbs chain_ζAbs chain_βconfig chain_βCommon chain_εref chain_δref chain_tolRef chain_ζActive chain_τ chain_tolLocal chain_ζLocal chain_τParent chain_tolParent chain_ζParent chain_epsBal chain_ζBal chain_ζCut chain_ζCfg chain_rowErr chain_ζCommon chain_ζWide chain_ζRow
      chain_size chain_a₀ chain_b₀ chain_e₀ chain_f₀ P Dv mm β ε Vort π hπ (Vort.length-1) chain_s₀ chain_p chain_kval chain_q chain_s false false chain_weightParent chain_weight outcome;
  (∀i ≤ (Vort.length-1),SuccessorSequenceWeightConditions (P.comap (markedVortexVertexEmbedding Vort i))
      (markedVortexPermutation Vort π hπ i) (3*d) (2*(Fintype.card (markedVortexHubType Vort i):ℝ)/initialIndexDensity (Fin (Dclass/2)) Dv)
      chain_τParent (successorWeightLower chain_k₀ (chain_αParent/4)) (successorWeightUpper chain_k₀ (chain_αParent/4)) (chain_weightParent i)) ∧
  (∀i ≤ (Vort.length-1)+1,SuccessorSequenceWeightConditions (P.comap (markedVortexActiveVertexEmbedding Vort i))
      (markedVortexActivePermutation Vort π hπ i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Vort i):Finset (markedVortexHubType Vort i)).card):ℝ)/initialIndexDensity (Fin (Dclass/2)) Dv)
      chain_τ (successorWeightLower chain_k₀ (chain_αParent/4)) (successorWeightUpper chain_k₀ (chain_αParent/4)) (chain_weight i)) ∧
  (MarkedVortexGeometricRecordEvent Vort chain_α chain_ρ₀ chain_κ chain_hIcut chain_ξ chain_xiDeep chain_ω chain_x chain_N chain_NI (Vort.length-1)) ∧
  Common (markedExpandedActualSelected π d z) ∧ Parent (markedExpandedActualSelected π d z) ∧ (
    let Result:=fun (S:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)) (ζRet ζChange:ℝ)=>
        ∃(Pack:Finset (Sym2 (Fin n))) (E:(Fin (Dclass/2))→Finset (Sym2 (Fin n))) (Spokes:(Fin (Dclass/2))→Finset (Fin n))
          (A:Finset (Fin n×Fin n)),
          let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E;
          Small.edgeFinset=A.image (fun aMatch=>s(aMatch.1,aMatch.2)) ∧
          LongFactorComplementProvenance F S P π d (r+4) (fun e=>rawExpandedApproximateCollapse e (z.1 e)) (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 Pack E A Spokes ∧
          ∃T:Finset {aMatch:Fin n×Fin n // longEligibleResidualArc M Small ⊥ aMatch},
          ∃τ:RawMarkedOutcome (Fin n) (Fin (Dclass/2)) Bool Bool,
          (∀mark x y,markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
            if mark then ∃e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
            else ∃e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧e.val.val.2=y) ∧
          let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun x=>rawExpandedApproximateCollapse (Sum.inr x) (z.1 (Sum.inr x))) false (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 w=>d) Subtype.val
          let Hnew:Bool→Fin n→(Fin (Dclass/2))→Prop:=fun b v w=>if b then retainedRawMarkedSpokes π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1 (Sum.inr e))) false (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false true true v w else v∈Spokes w\Y w;
          FirstVortexNamedLevelChainContinuation P π d r Dv mm β ε Vort hπ (Vort.length-1) z τ Hnew active (markedExplicitJointLocalCap (r+4) (r+12) etaBal x) ζChange εStable (2*mm) eStable
        let m:ℝ:=(r+4:ℕ)
        let ρ:=initialIndexDensity (Fin (Dclass/2)) Dv
        let p:ℝ:=ρ*(1/100)/2
        let k:ℝ:=ρ*((1/100)/m)/2
        let q:=longAssignedIntervalProbability F hF K (r+4) θ
        let p₂:ℝ:=(∑w,longAssignedApproxOrdinaryWeight F hF K (r+4) θ w)/(Dv:ℝ)
        let k₂:ℝ:=(∑w,longAssignedApproxMarkedWeight F hF K (r+4) θ w)/(Dv:ℝ)
        let u:ℝ:=2*(∑w,(1-1/100-(1/100)/m-longAssignedApproxMarkedWeight F hF K (r+4) θ w-
          longAssignedApproxOrdinaryWeight F hF K (r+4) θ w))/(Dv:ℝ)
        let σ:=fun e:Sym2 (Fin n)=>z.1 (Sum.inl e);
        (((∀T:SimpleGraph (Fin n),(∀v,T.degree v≤eRob)→
          ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card (Fin (Dclass/2))) ∧
            (∀x y,((spanningRestriction (⊤:SimpleGraph (Fin n)) (Vort.extendedVertices 1))⊔T).Adj x y→
              (S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
            (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)) ∧ (((RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) false
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
          (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret z.2 ∧
          (∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) Finset.univ v).card:ℝ)≤
            4*(Fintype.card (Fin (Dclass/2)):ℝ)/d+4*(n:ℝ)^(3/4:ℝ))) ∧ (∀(j:Fin 6) (v:Fin n),
          |((∑x,sampledColourOrientation P σ j v x:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ) ∧
          |((∑x,sampledColourOrientation P σ j x v:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ) ∧
          |(sampledColourDegree P (fun e=>(σ e).1) j v:ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j*P.degree v|<(n:ℝ)^(3/5:ℝ))) ∧ (∀g v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g v).card:ℝ)-(∑w,q w g/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))))) ∧
        ∃boundary lossInside inside loc:ℝ,
        boundary=4*(Fintype.card (Fin (Dclass/2)):ℝ)/d+4*(n:ℝ)^(3/4:ℝ) ∧
        FirstVortexSummedLossAt n d ((markedVortexInnerVertices Vort 0).card:ℝ)
          (markedExplicitJointLocalCap (r+4) (r+12) etaBal x) rhoMatch etaMatch θ aMatch γMatch ξClass κPack Δ ζret ηBalance boundary lossInside inside loc ∧
        ∃D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)),
        ∃C:Finset (Finset (Fin n)⊕(Fin n×Fin (Dclass/2))),
        longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1)
          γLoss σLoss eRob (Vort.extendedVertices ((Vort.length-1)+1)) (Vort.extendedIndices ((Vort.length-1)+1)) D₀ C ∧
        let Match:=fun (S:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n))=>
          LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv aMatch γMatch epsMatch βList F hF weight w D₀ C S M Del ∧
          FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign epsMatch δlocal δglobal ((2*αSelected)/2) bmatch ρ₀ ξPrepared Δ aMatch γMatch weight w z.1
            (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2;
        ((∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card (Fin (Dclass/2)))→
          (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
          (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
          markedResourceRimGraph C≤S→∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
          S≤P ∧ S.IsRegularOfDegree (2*Fintype.card (Fin (Dclass/2))) ∧
          (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
          (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) ∧
          markedResourceRimGraph C≤S ∧
          (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
          LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv aMatch γMatch epsMatch βList F hF weight w D₀ C S M Del ∧
          FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign epsMatch δlocal δglobal ((2*αSelected)/2) bmatch ρ₀ ξPrepared Δ aMatch γMatch weight w z.1
            (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2 ∧
        (0<K→θ≤1→∀ζRet:ℝ,0<active→0<ε→ε≤1/4→0<mm→0≤ζRet→ζRet≤active/128→ζret≤ζRet*ε/2→
          ∀p₂' k₂' u':ℝ,
          (∀v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false v).card:ℝ)-(∑w,q w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
          (∀j v,|((∑x,sampledColourOrientation P σ j x v:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂' k₂' u' j/2*P.degree v|<(n:ℝ)^(3/5:ℝ))→
          0≤γMatch→0≤θ→u'≤2*θ→
          (∀v,|(sampledColourDegree P (fun e=>(σ e).1) 4 v:ℝ)-u'*(P.degree v:ℝ)|≤(n:ℝ)^(3/5:ℝ))→
          ∀ζChange:ℝ,0≤ζChange→ζChange≤capStable→active≤ζChange→(min cap (1:ℝ))/2≤ζChange→
            0≤(markedExplicitJointLocalCap (r+4) (r+12) etaBal x)→active≤(markedExplicitJointLocalCap (r+4) (r+12) etaBal x)→Result S M Del ζRet ζChange) ))) ∧
        (∀rho omega t:ℝ,chain_ρ₀ ≤ rho → rho ≤ 1 → chain_ρ₀/8 ≤ omega → omega ≤ 1 → chain_tstar ≤ t → (r+4:ℝ)*t ≤ 1 → 
      chain_ρ₀/400 ≤ rho*(r+4:ℝ)*t/2 → chain_kstar ≤ rho*(r+4:ℝ)*t/2 → chain_kstar ≤ rho*t/2 → chain_kstar ≤ t → 
      ∀(Gamma Shade:Type) [Fintype Gamma] [Fintype Shade],
      ∀level:MarkedReferenceLevelData Gamma Shade r d chain_N chain_NI chain_Kgeom (chain_α/16) rho omega t chain_kstar chain_βA
        (successorWeightLower chain_k₀ (chain_α/4)) (successorWeightUpper chain_k₀ (chain_α/4))
        chain_κ chain_ξ chain_thetaDeep (chain_α/8) chain_ω (ε/4) chain_βrec (successorWeightLower chain_k₀ (chain_α/4)) (successorWeightUpper chain_k₀ (chain_α/4))
        chain_eta chain_x (chain_ρ₀/16) chain_hIcut chain_deltaI chain_etaBal,
      MarkedReferenceLevelStepProperty level (γCore+extra) (σCore+extra)) ∧ ε≤εStable):
    ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card (Fin (Dclass/2))) ∧ HasFactorDecomposition S F :=by
  obtain ⟨weightParent,weightActive,levelWeight,z,hParentWeight,hActiveWeight,hGeo,hCommon,hGood,hInput,hSteps,hStable⟩:=hBundle
  have hLocalEq:(markedExplicitJointLocalCap (r+4) (r+12) etaBal x)=markedExplicitJointLocalCap (r+4) (r+12) etaBal x:=rfl
  have hL:Vort.length-1+1=Vort.length:=by have hh:=Vort.length_pos; omega
  have hN:1≤NGeom d:=hNGeom d (by omega)
  have hBudget:Classical.choose (marked_vortex_terminal_budget eStable γLevel σLevel hγ hσ)≤Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using hBudgetHost.trans hnHost
  let Common:=fun (outcome:RawMarkedRetainedOutcome (U:=Fin (Dclass/2)) (Color:=Bool) π d false)=>
    LongMatchingCommonEvent P π Dv mm β ε Vort hπ r K d (2*mm) aCommon bCommon eCommon aRob bRob eRob fCommon (Vort.length-1) hNbr
      F hF θ (initialIndexDensity (Fin (Dclass/2)) Dv) βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent (κ/2) (min αRef (1/2:ℝ)/2) (1/(200*((r+4:ℕ):ℝ))) ζEvent
      εSelected ζSelected εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀ (1/100:ℝ) (ρ₀/(800*((r+4:ℕ):ℝ))) τLevelEvent levelWeight outcome
  let Parent:=fun (outcome:RawMarkedRetainedOutcome (U:=Fin (Dclass/2)) (Color:=Bool) π d false)=>
    MarkedVortexParentRecordSmallerReferenceEvent r (r+12) (k₀) d (2*αRef) (ρ₀) ((1/100:ℝ)) ((1/(200*((r+4:ℕ):ℝ)))) ((ρ₀/(800*((r+4:ℕ):ℝ))))
      (εAbsP) (ζAbsP) (βconfigP) (βCommonP) (εRef) (κ/2) (δSelected) (δSelected) (δSelected) (δSelected) (δSelected) (δSelected) (δSelected) (δSelected) (εSelected) (ζSelected) (δSelected) (δSelected) (δSelected) (δSelected) (δSelected) (δSelected)
      ((2*mm)) (aParent) (bParent) (eParent) (fCommon) P Dv mm β ε Vort π hπ (Vort.length-1) ((1/100:ℝ)) ((initialIndexDensity (Fin (Dclass/2)) Dv*(1/100:ℝ)/2)) ((initialIndexDensity (Fin (Dclass/2)) Dv*(1/100:ℝ)/2/((r+4:ℕ):ℝ))) ((longAssignedIntervalProbability F hF K (r+4) θ)) ((longAssignedSpokeProbability F hF K (r+4) θ)) false false (weightParent) (weightActive) outcome
  have hSteps' := hSteps
  rw [hγSplit,hσSplit] at hSteps'
  try dsimp only [] at hInput
  obtain ⟨hExpanded,boundary,lossInside,inside,loc,hBoundary,hSum,D₀,C,hTerminal,hFor⟩:=hInput
  have hSelected:=first_vortex_concrete_factor_selection hn hK hDpos P π d r F hF θ ρ₀ γMatch hθ hθ1 hρ₀ hγMatch hρlo hρhi
    ε active t c ζret ζlocal ηBalance κaux cap capStable (markedExplicitJointLocalCap (r+4) (r+12) etaBal x) mm hε hε1 hmm hret hactive hcap hcapStable hactiveGlobal hactiveLocal
    αRef κ ζFixed thetaDeep (successorWeightUpper k₀ ((2*αRef)/4)) hα hChosen z Parent Common hGood hCommon β Vort hπ (2*αRef) ξClass γLoss σLoss hεHost (Vort.length-1) eRob εStable (2*mm) eStable D₀ C hTerminal (RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret z.2 ∧
      (∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) Finset.univ v).card:ℝ)≤
        4*(Fintype.card (Fin (Dclass/2)):ℝ)/d+4*(n:ℝ)^(3/4:ℝ)))
    lamAssign epsMatch δlocal δglobal ((2*αSelected)/2) bmatch ξPrepared Δ aMatch βList weight w hExpanded hFor
  dsimp only [] at hSelected
  obtain ⟨hParent,hCommon,S,M,Del,ζChange,hSP,hReg,hζChange,hParentCap,⟨hMatch,hPrepared⟩,hSeed⟩:=hSelected
  refine ⟨S,hSP,hReg,?_⟩
  exact first_vortex_selected_level_factor_from_seed hEven P π d r Dv mm β ε Vort hπ (Vort.length-1) z active (markedExplicitJointLocalCap (r+4) (r+12) etaBal x) ζChange εStable (2*mm) eStable
    F hF θ k₀ (NGeom d) NI Kgeom (2*mm) aParent bParent eParent fCommon αRef ρ₀ δSelected εSelected ζSelected εAbsP ζAbsP βconfigP βCommonP εRef
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut weightParent weightActive hα hρ₀ hρlo hκ hx hθDeep heta hd hε hxi0 hXiScale hTstar hDeepSource
    δbase ζFixed ζCut cap₁ cap₂ hAt hβA hrec hεRef hL hβ hIcut0 hEtaBal hδAlpha hδStar hδTime hIStar hδbaseCut hCut
    hN hn hU hDpos hDlo hρhi hζChange hζFixed hCycleFixed hPathFixed hβrecT hActiveCap hLocalEq hParentCap
    S Del hdReconstruct hnoshort Dv aMatch γMatch epsMatch Δ βList weight w D₀ C M hMatch hSeed
    γLevel σLevel hγ hσ hParentWeight hActiveWeight hGeo hGood hSteps' hStable (le_refl _) hBudget
end Oberwolfach
