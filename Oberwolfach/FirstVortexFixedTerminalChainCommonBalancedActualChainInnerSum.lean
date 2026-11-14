module

public import Oberwolfach.FirstVortexFixedTerminalChainCommonBalancedRobustMatchingInnerSum
public import Oberwolfach.FirstVortexConcreteCommonBalancedActualChainInnerSum
public import Oberwolfach.FirstVortexConcreteFixedClassCommonBalancedRobustMatchingInnerSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance fixedTerminalChainActualInnerFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) fixedTerminalChainActualInnerSix : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance fixedTerminalChainActualInnerArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem first_vortex_fixed_terminal_chain_common_balanced_actual_chain_inner_sum
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
    ∀(Chain:∀D:MarkedReferenceDeletion P π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)),
        Finset (Finset (Fin n)⊕(Fin n×U))→Prop)
      (Dsel:MarkedReferenceDeletion P π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)))
      (Csel:Finset (Finset (Fin n)⊕(Fin n×U))),
      longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1)
        γLoss σLoss e₀ (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) Dsel Csel →
      Chain Dsel Csel →
      LongBoundaryPreparedClasses P π d r Dv mm β ε Vort z θ a γ eps βList ξPart Δ
        lamAssign δlocal δglobal α bmatch ρ₀ ξ F hF weight w Dsel Csel →
    ∀(αAssign ρreserve:ℝ), αAssign/2=α → (e₀:ℝ)≤ρreserve*n → e₀≤e →
    ∀(βfinal κ boundary loc lossInside inside δsmall ρsmall δspoke:ℝ),
    0<Fintype.card U → ε≤δglobal → 0<βfinal → βfinal≤1 →
    δglobal≤(βfinal/100)^2 → 0<n → 100/βfinal≤(n:ℝ) →
    2/Real.sqrt δglobal≤(n:ℝ) → Fintype.card U≤n →
    0<κ → (hδsmall:0<δsmall) → (hθsmall:10*θ≤δsmall) →
    Classical.choose (first_vortex_all_hub_small_load_from_tests δsmall θ d hδsmall hθ hθsmall hspacing)≤n →
    ρsmall≤θ/4096 →
    max a γ*n≤ρsmall*n → εInner*n+((6*d+2:ℕ):ℝ)≤δsmall*n/4 →
    0≤δspoke → δsmall+κ≤Real.sqrt δspoke →
    2*(δsmall*n+(κ*n+1))≤δLoss*n → 10*θ≤κ*(βfinal/4) →
    δglobal≤(βfinal/200)^2 → 200/βfinal≤(n:ℝ) →
    0≤loc → 0≤ inside → 4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)≤boundary →
    loc≤eta*n → inside≤((Vort.extendedVertices 1).card:ℝ)*eta*n →
    0≤2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1)) →
    ((Vort.extendedVertices 1).card:ℝ)*(Δ*n+2*((6*d+2:ℕ):ℝ))+
      (n:ℝ)*(2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1)))≤lossInside →
    ((Vort.extendedVertices 1).card:ℝ)*((n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ))+lossInside≤ inside →
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
    (longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1)
      γLoss σLoss e₀ (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) Dsel Csel ∧ Chain Dsel Csel) ∧
    ∀S:SimpleGraph (Fin n),S≤P → S.IsRegularOfDegree (2*Fintype.card U) →
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n) →
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) → markedResourceRimGraph Csel≤S →
    ∃Mhost:Fin n→Fin n→ℕ, ∃Del:SimpleGraph (Fin n),
      S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n) ∧
      (∀x∈(Vort.extendedVertices 1),∀y∈(Vort.extendedVertices 1),S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph Csel≤S ∧
      (∀x∈(Vort.extendedVertices 1),∀y∈(Vort.extendedVertices 1),(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w Dsel Csel S Mhost Del ∧
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
      (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+(loc+(inside/(n:ℝ)+loc)/rho+1))≤cLocal*((markedVortexInnerVertices Vort 0).card:ℝ)→
    (2*(ζret*n+((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1)))+
      ((ηBalance*n)+2*((2*θ+2*max a (4*γ)+2*ξPart)*n+2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1))+
        (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+(loc+(inside/(n:ℝ)+loc)/rho+1))))≤cLocal*((markedVortexInnerVertices Vort 0).card:ℝ)→
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
      let DelPlus:=Del⊔markedResourceRimGraph Csel
      let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E
      let Peligible:=longEligibleResidualArc Mhost Small ⊥
      let T₁:=longDualInitialMarked P (fun x=>z.1 (Sum.inl x)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
      ∃T:Finset {x:(Fin n)×(Fin n) // Peligible x},
      (∀v,((changed ((longSelectedPhysicalGraph P π d z.1).neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤
        ((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(δsmall*n+(κ*n+1)))+(n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)) ∧
      Pack=Used.edgeFinset ∧ Pack⊆(longApproximatePhysicalGraph P π d z.1).edgeFinset ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δglobal*Fintype.card (Fin n)) ∧
      (∀x y,Small.Adj x y→¬(markedResourceRimGraph Csel).Adj x y) ∧
      (∀v,directedInCount Peligible T v=d*startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) ∧
      (∀x∈T,longMarkedArcEligible π d x.val) ∧ (∀x,x∉T→longOrdinaryArcEligible π d x.val) ∧
      (∀x,x.val.1∈(Vort.extendedVertices 1)→(x∈T↔x∈T₁)) ∧
      (∀x,Sum.inl ({x.val.1,x.val.2}:Finset (Fin n))∈Csel→(x∈T↔x∈T₁)) ∧
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
          loc+(inside/(n:ℝ)+loc)/rho+1) ∧
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
              (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+(loc+(inside/(n:ℝ)+loc)/rho+1)) ∧
          (∀b v w,¬(Hraw b v w↔(if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false true true v w else v∈Spokes w\Y w))→FS.Adj (Sum.inl v) (Sum.inr w)) ∧
          (∀x,(FS.degree x:ℝ)≤ζChange*n) ∧
          (∀B:Finset U,∀v,v∉(Vort.extendedVertices 1)→(∑w∈B,if ¬(Hraw false v w↔v∈Spokes w\Y w) then (1:ℝ) else 0)≤
            2*(ζret*n+((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1)))+
              ((ηBalance*n)+2*((2*θ+2*max a (4*γ)+2*ξPart)*n+2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1))+
                (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+(loc+(inside/(n:ℝ)+loc)/rho+1)))) ∧
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
        ∧ (let W:=↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))
           let Z:=markedVortexNonDeeperHubType Vort 0
           let f:=markedVortexActiveVertexEmbedding Vort 1
           let g:=markedVortexNonDeeperHubToPhysical Vort 0
           let HL:=fun b v u=>Hraw b (f v) (g u)
           let HL':=fun b v u=>if b then Hraw true (f v) (g u) else Hnew false (f v) (g u)
           let FSactive:=markedSpokeChangeGraph HL HL';
  ∀(chain_k₀:ℕ),
  ∀(chain_α chain_ρ₀ chain_sstar chain_tstar chain_kstar:ℝ),
  ∀(chain_εAbs chain_ζAbs chain_βconfig chain_βCommon chain_εref chain_δref chain_tolRef chain_ζActive chain_τ chain_tolLocal chain_ζLocal chain_τParent chain_tolParent chain_ζParent chain_epsBal chain_ζBal chain_ζCut chain_ζCfg chain_rowErr chain_ζCommon chain_ζWide chain_ζRow:ℝ),
  ∀(chain_size chain_a₀ chain_b₀ chain_e₀ chain_f₀:ℕ),
  ∀(chain_s₀ chain_p chain_kval:ℝ),
  ∀(chain_q:U → Bool → ℝ),
  ∀(chain_s:U → Bool → ℝ),
  ∀(chain_weightParent:∀i,(Fin (r+4+1) → markedVortexVertexType Vort i) → ℝ),
  ∀(chain_weight:∀i,(Fin (r+4+1) → ↥((Finset.univ\markedVortexInnerVertices Vort i):Finset (markedVortexVertexType Vort i))) → ℝ),
  ∀(chain_βA chain_βrec chain_κ chain_ξ chain_thetaDeep chain_ω chain_xiDeep chain_etaBal chain_x chain_eta chain_deltaI chain_hIcut chain_αParent chain_κold chain_xold chain_thetaOld chain_etaOld:ℝ),
  ∀(chain_N chain_NI chain_Kgeom:ℕ),
  ∀(chain_hα:0<chain_α),
  ∀(chain_hαle:chain_α ≤ chain_αParent),
  ∀(chain_hκle:chain_κold ≤ chain_κ),
  ∀(chain_hxle:chain_xold ≤ chain_x),
  ∀(chain_hθle:chain_thetaOld ≤ chain_thetaDeep),
  ∀(chain_hηle:chain_etaOld ≤ chain_eta),
  ∀(chain_hρ:0  ≤  initialIndexDensity U Dv),
  ∀(chain_hs₀:0 ≤ chain_s₀),
  ∀(chain_hd:1 ≤ d),
  ∀(chain_he:0 ≤ ε),
  ∀(chain_hp:chain_p=initialIndexDensity U Dv*chain_s₀/2),
  ∀(chain_hk:chain_kval=chain_p/(((r+4):ℕ):ℝ)),
  ∀(chain_hq0:∀u,chain_q u false=chain_s₀/(((r+4):ℕ):ℝ)),
  ∀(chain_hs0:∀u,chain_s u false=chain_s₀),
  ∀(chain_hXi0:0 ≤ chain_xiDeep),
  ∀(chain_hXiScale:(4*chain_Kgeom+3*r+50:ℝ)*chain_xiDeep ≤ chain_κ/2),
  ∀(chain_hDeepGap:(1+2/initialIndexDensity U Dv)*chain_xiDeep ≤ (chain_s₀/(((r+4):ℕ):ℝ))*chain_ω/32),
  ∀(chain_hParentWeight:∀i ≤ L,SuccessorSequenceWeightConditions (P.comap (markedVortexVertexEmbedding Vort i))
      (markedVortexPermutation Vort π hπ i) (3*d) (2*(Fintype.card (markedVortexHubType Vort i):ℝ)/initialIndexDensity U Dv)
      chain_τParent (successorWeightLower chain_k₀ (chain_αParent/4)) (successorWeightUpper chain_k₀ (chain_αParent/4)) (chain_weightParent i)),
  ∀(chain_hActiveWeight:∀i ≤ L+1,SuccessorSequenceWeightConditions (P.comap (markedVortexActiveVertexEmbedding Vort i))
      (markedVortexActivePermutation Vort π hπ i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Vort i):Finset (markedVortexHubType Vort i)).card):ℝ)/initialIndexDensity U Dv)
      chain_τ (successorWeightLower chain_k₀ (chain_αParent/4)) (successorWeightUpper chain_k₀ (chain_αParent/4)) (chain_weight i)),
  ∀(chain_hGeo:MarkedVortexGeometricRecordEvent Vort chain_α chain_ρ₀ chain_κ chain_hIcut chain_ξ chain_xiDeep chain_ω chain_x chain_N chain_NI L),
  ∀(chain_hGood:MarkedVortexParentRecordSmallerReferenceEvent r (r+12) chain_k₀ d chain_αParent chain_ρ₀ chain_sstar chain_tstar chain_kstar
      chain_εAbs chain_ζAbs chain_βconfig chain_βCommon chain_εref chain_δref chain_tolRef chain_ζActive chain_τ chain_tolLocal chain_ζLocal chain_τParent chain_tolParent chain_ζParent chain_epsBal chain_ζBal chain_ζCut chain_ζCfg chain_rowErr chain_ζCommon chain_ζWide chain_ζRow
      chain_size chain_a₀ chain_b₀ chain_e₀ chain_f₀ P Dv mm β ε Vort π hπ L chain_s₀ chain_p chain_kval chain_q chain_s false false chain_weightParent chain_weight (markedExpandedActualSelected π d z)),
  ∀(chain_hβA:chain_βA ≤ chain_βCommon),
  ∀(chain_hζκ:chain_ζCommon ≤ chain_κold/4),
  ∀(chain_hC:3*chain_βA ≤ markedLocalCycleCoefficient r (chain_αParent/2) (chain_tstar/2) chain_kstar-(r+5:ℕ)*chain_ζCfg),
  ∀(chain_hP:3*chain_βA ≤ markedLocalPathCoefficient r (chain_αParent/2) (chain_tstar/2) chain_kstar-(r+4:ℕ)*chain_ζCfg),
  ∀(chain_hrec:chain_βrec ≤ chain_βA),
  ∀(chain_herr:chain_tolRef+(r+12:ℕ)*chain_ζActive ≤ chain_κold/4),
  ∀(chain_hζActiveK:chain_ζActive ≤ chain_κold/4),
  ∀(chain_hεeq:chain_εref ≤ chain_κold/4),
  ∀(chain_hδeq:chain_δref=chain_κold),
  ∀(chain_hpot:chain_τParent+chain_tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper chain_k₀ (chain_αParent/4)/(chain_ρ₀*chain_sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*chain_ζParent ≤ chain_κold/4),
  ∀(chain_hdeep:chain_τParent+chain_tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper chain_k₀ (chain_αParent/4)/(chain_ρ₀*chain_sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*chain_ζParent ≤ chain_thetaOld/4),
  ∀(chain_hxold:0 ≤ chain_xold),
  ∀(chain_hbal:chain_epsBal+((r+4)+2:ℕ)*chain_ζBal ≤ chain_etaBal),
  ∀(chain_hmargin:chain_epsBal+((r+4)+2:ℕ)*chain_ζBal ≤ chain_xold/2),
  ∀(chain_hterminal:L+1=Vort.length),
  ∀(chain_hrowmargin:chain_rowErr+chain_ζRow ≤ (chain_s₀/((r+4:ℕ):ℝ))/8),
  ∀(chain_hloadmargin:chain_τ+chain_tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper chain_k₀ (chain_αParent/4)/(chain_ρ₀*chain_sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*chain_ζWide ≤ chain_etaOld/4),
  ∀(chain_hbquarter:β ≤ 1/4),
  ∀(chain_hh:0 ≤ chain_hIcut),
  ∀(chain_hδα:chain_deltaI ≤ (chain_αParent/2)/32),
  ∀(chain_hδstar:chain_deltaI ≤ chain_kstar/32),
  ∀(chain_hδt:2*chain_deltaI ≤ chain_tstar/8),
  ∀(chain_hhstar:2*chain_hIcut ≤ (chain_αParent/2)*chain_kstar/4),
  ∀(chain_hhs:2*chain_hIcut ≤ chain_tstar/8-chain_ζCut),
  ∀(chain_hEndpoint:chain_tolRef+(r+12:ℕ)*chain_ζActive ≤ chain_xold/2),
  ∀(chain_iota:ℝ),
  ∀(chain_hηBalPos:0<chain_etaBal),
  ∀(chain_hxPos:0<chain_x),
  ∀(chain_hiota:0 < chain_iota),
  ∀(chain_hζchange:0 ≤ ζChange),
  ∀(chain_hepsBal:0 ≤ chain_epsBal),
  ∀(chain_hζBal:0 ≤ chain_ζBal),
  ∀(chain_hBalRelative:chain_epsBal+((r+4)+2:ℕ)*chain_ζBal ≤ chain_etaBal/2),
  ∀(chain_hBalAmbient:chain_epsBal+((r+4)+2:ℕ)*chain_ζBal ≤ chain_x/4),
  ∀(chain_hsize:chain_iota*Fintype.card (markedVortexVertexType Vort 0) ≤ ((markedVortexInnerVertices Vort 0).card:ℝ)),
  ∀(chain_hn:0<Fintype.card (Fin n)),
  ∀(chain_hu:Fintype.card U ≤ Fintype.card (Fin n)),
  ∀(chain_pstar:ℝ),
  ∀(chain_hpstar:0<chain_pstar),
  ∀(chain_hplo:chain_pstar ≤ chain_p),
  ∀(chain_hklo:chain_pstar ≤ chain_kval),
  ∀(chain_hslo:chain_pstar ≤ chain_s₀),
  ∀(chain_hp1:chain_p ≤ 1),
  ∀(chain_hk1:chain_kval ≤ 1),
  ∀(chain_hs1:chain_s₀ ≤ 1),
  ∀(chain_hDlo:(Fintype.card (markedVortexVertexType Vort 0):ℝ)/2 ≤ 2*(Fintype.card (markedVortexHubType Vort 0):ℝ)/initialIndexDensity U Dv),
  ∀(chain_hDhi:2*(Fintype.card (markedVortexHubType Vort 0):ℝ)/initialIndexDensity U Dv ≤ 2*Fintype.card (markedVortexVertexType Vort 0)),
  ∀(chain_hboundaryHalf:chain_xold ≤ chain_x/2),
  ∀(chain_hκPos:0<chain_κ),
  ∀(chain_hωPos:0<chain_ω),
  ∀(chain_plo chain_klo:ℝ),
  ∀(chain_hploPos:0<chain_plo),
  ∀(chain_hkloPos:0<chain_klo),
  ∀(chain_hαeq:chain_αParent=2*chain_α),
  ∀(chain_hκoldEq:chain_κold=chain_κ/2),
  ∀(chain_hUlower:chain_ω*Fintype.card (Fin n) ≤ (Fintype.card U:ℝ)),
  ∀(chain_hpLower:chain_plo ≤ chain_p),
  ∀(chain_hkLower:chain_klo ≤ chain_kval),
  ∀(chain_ζFixed:ℝ),
  ∀(chain_hζFixed:0<chain_ζFixed),
  ∀(chain_hCfg:2*chain_ζCfg ≤ chain_ζFixed),
  ∀(chain_hθDeepPos:0<chain_thetaDeep),
  ∀(chain_hθoldHalf:chain_thetaOld ≤ chain_thetaDeep/2),
  ∀(chain_hcycleDeep:3*chain_βA ≤ markedLocalCycleCoefficient r (chain_αParent/2) (chain_tstar/2) chain_kstar-(r+5:ℕ)*chain_ζFixed),
  ∀(chain_hpathDeep:3*chain_βA ≤ markedLocalPathCoefficient r (chain_αParent/2) (chain_tstar/2) chain_kstar-(r+4:ℕ)*chain_ζFixed),
  ∀(chain_hηPos:0<chain_eta),
  ∀(chain_htstarPos:0<chain_tstar),
  ∀(chain_hnactive:0<Fintype.card ↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))),
  ∀(chain_hβrect:chain_βrec ≤ (chain_s₀/((r+4:ℕ):ℝ))/4),
  ∀(chain_htt:chain_tstar ≤ chain_s₀/((r+4:ℕ):ℝ)),
  ∀(chain_hactiveErr:chain_τ+chain_tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper chain_k₀ (chain_αParent/4)/(chain_ρ₀*chain_sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*chain_ζWide ≤ chain_eta/8),
  ∀(chain_hactiveRow:chain_rowErr+chain_ζRow ≤ chain_tstar/16),
  ∀(chain_hDactiveLo:(Fintype.card ↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1)):ℝ)/2 ≤ 
      2*((((Finset.univ\markedVortexInnerHubs Vort 1):Finset (markedVortexHubType Vort 1)).card):ℝ)/initialIndexDensity U Dv),
  ∀(chain_hDactiveHi:2*((((Finset.univ\markedVortexInnerHubs Vort 1):Finset (markedVortexHubType Vort 1)).card):ℝ)/initialIndexDensity U Dv ≤ 
      2*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))),
  ∀(chain_hρ₀Pos:0<chain_ρ₀),
  ∀(chain_hρlo:chain_ρ₀ ≤ initialIndexDensity U Dv),
  ∀(chain_hρhi:initialIndexDensity U Dv ≤ 1),
  ∀(chain_htstarCap:chain_tstar ≤ (1/100)/(((r+4):ℕ):ℝ)),
  ∀(chain_hkstarPos:0<chain_kstar),
  ∀(chain_hkstarCap:chain_kstar ≤ initialIndexDensity U Dv*((1/100)/(((r+4):ℕ):ℝ))/2),
  ∀(chain_hs₀Eq:chain_s₀=(1/100:ℝ)),
  ∀(chain_hcLocalEq:cLocal=Classical.choose ((marked_vortex_initial_balance_from_parent_ambient_local_changes r chain_x chain_hxPos).2 chain_etaBal chain_hηBalPos)),
  ∀(chain_hζFinal:ζChange ≤ Classical.choose (marked_vortex_fixed_margin_local_correction_cap r chain_κ chain_αParent chain_ω chain_plo chain_klo chain_tstar chain_kstar chain_ζFixed chain_thetaDeep chain_eta
      (successorWeightUpper chain_k₀ (chain_αParent/4)) chain_pstar chain_etaBal chain_x chain_iota
      chain_hκPos (lt_of_lt_of_le chain_hα chain_hαle) chain_hωPos chain_hploPos chain_hkloPos chain_htstarPos chain_hζFixed chain_hθDeepPos chain_hηPos
      (successorWeightConstants_pos chain_k₀ (chain_αParent/4) (by have chain_hh:=lt_of_lt_of_le chain_hα chain_hαle;positivity)).2.le
      chain_hpstar chain_hηBalPos chain_hxPos chain_hiota)),
        (∀rho omega t:ℝ,chain_ρ₀ ≤ rho → rho ≤ 1 → chain_ρ₀/8 ≤ omega → omega ≤ 1 → chain_tstar ≤ t → (r+4:ℝ)*t ≤ 1 → 
      chain_ρ₀/400 ≤ rho*(r+4:ℝ)*t/2 → chain_kstar ≤ rho*(r+4:ℝ)*t/2 → chain_kstar ≤ rho*t/2 → chain_kstar ≤ t → 
      ∀(Gamma Shade:Type) [Fintype Gamma] [Fintype Shade],
      ∀level:MarkedReferenceLevelData Gamma Shade r d chain_N chain_NI chain_Kgeom (chain_α/16) rho omega t chain_kstar chain_βA
        (successorWeightLower chain_k₀ (chain_α/4)) (successorWeightUpper chain_k₀ (chain_α/4))
        chain_κ chain_ξ chain_thetaDeep (chain_α/8) chain_ω (ε/4) chain_βrec (successorWeightLower chain_k₀ (chain_α/4)) (successorWeightUpper chain_k₀ (chain_α/4))
        chain_eta chain_x (chain_ρ₀/16) chain_hIcut chain_deltaI chain_etaBal,
      MarkedReferenceLevelStepProperty level γLoss σLoss) → ε≤εStable → 2*mm≤sizeStable →
    ∀(hγ:0<γLoss) (hσ:0<σLoss),
    Classical.choose (marked_vortex_terminal_budget eStable γLoss σLoss hγ hσ)≤Fintype.card (Fin n) →
    let Earc:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let Karc:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true;
    HasResourceDecomposition (fun W:MarkedWheel (fun e:Earc=>e.val.1) (fun e=>e.val.2)
      (fun e:Karc=>e.val.1) (fun e=>e.val.2) (r+4) π (3*d) (Hnew false) (Hnew true)=>markedWheelPhysicalResources W)
      (markedDecompositionTarget (markedPhysicalRimSet (fun e:Earc=>e.val.1) (fun e=>e.val.2)
        (fun e:Karc=>e.val.1) (fun e=>e.val.2) π) (Hnew false) (Hnew true)))
 :=by
  obtain ⟨N,hN⟩:=first_vortex_fixed_terminal_chain_common_balanced_robust_matching_inner_sum α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
    hα hlam hε hδ hδ1 hθ hepsPos hρ₀ hbmatch hαb hbd hεsmall hθδ hθlocal hθhi hlamlocal hspacing hd hK hm heps hξ hξ0
    hρ₀hi hδglobal hθglobal hprecise ξCap hξPartCap hCap hlamθ hdlarge Nret hNret hrho heta hetaR hbudget hsupply
  refine ⟨N,?_⟩
  intro n hn _ U _ _ P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ ρ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z ζselect hζselect Inner βList terr τerr hτerr hEvent
  intro γLoss σLoss size a₀ b₀ e₀ f₀ L Bpart εAbs ζCorr ξCorr hsize hL hπ hξCorr hbudgetCorr heAbs heB hEvery hProtected Chain Dsel Csel hTerminal hChain hPreparedClasses αAssign ρreserve hαAssign hReserveScale hee
  intro βfinal κ boundary loc lossInside inside δsmall ρsmall δspoke hU hεδ hβ hβ1 hδbound hn0 hnβ hnδ hu hκ hδsmall hθsmall hnsmall hρsmall hscale hbadsmall hδspoke hspokeScale hSharp hθκ hδstrong hnstrong hloc hinside hboundaryRate hlocGlobal hinsideGlobal hOuterNonneg hInsideBound hInsideBudget hlocalBudget hρreserve hListMargin hΔξ
  intro h hh sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon ρHost hρHost hsizeHost
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance hγRich levelWeight hCommon
    κaux κref hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hκauxRet
  intro εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable hstable
  have hc:=hN n hn
  have hd:fixedTerminalChainRobustInnerFin n=fixedTerminalChainActualInnerFin n:=Subsingleton.elim _ _
  have hdK:fixedTerminalChainRobustInnerFin K=fixedTerminalChainActualInnerFin K:=Subsingleton.elim _ _
  have hd6:fixedTerminalChainRobustInnerSix=fixedTerminalChainActualInnerSix:=Subsingleton.elim _ _
  try rw [hd] at hc
  try rw [hdK] at hc
  try rw [hd6] at hc
  obtain ⟨⟨hTermOut,hChainOut⟩,hFor⟩:=hc U P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ ρ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z ζselect hζselect Inner βList terr τerr hτerr hEvent
    γLoss σLoss size a₀ b₀ e₀ f₀ L Bpart εAbs ζCorr ξCorr hsize hL hπ hξCorr hbudgetCorr heAbs heB hEvery hProtected Chain Dsel Csel hTerminal hChain hPreparedClasses αAssign ρreserve hαAssign hReserveScale hee
    βfinal κ boundary loc lossInside inside δsmall ρsmall δspoke hU hεδ hβ hβ1 hδbound hn0 hnβ hnδ hu hκ hδsmall hθsmall hnsmall hρsmall hscale hbadsmall hδspoke hspokeScale hSharp hθκ hδstrong hnstrong hloc hinside hboundaryRate hlocGlobal hinsideGlobal hOuterNonneg hInsideBound hInsideBudget hlocalBudget hρreserve hListMargin hΔξ
    h hh sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon ρHost hρHost hsizeHost βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance hγRich levelWeight hCommon κaux κref hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hκauxRet εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable hstable
  refine ⟨⟨hTermOut,hChainOut⟩,?_⟩
  intro S hSP0 hregS0 hEdit0 hInner0 hRes0
  obtain ⟨Mhost,Del,hSP,hregS,hEdit,hInner,hRes,hCover,hwitness,hPrepared,hOut⟩:=hFor S hSP0 hregS0 hEdit0 hInner0 hRes0
  refine ⟨Mhost,Del,hSP,hregS,hEdit,hInner,hRes,hCover,hwitness,hPrepared,?_⟩
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
  have hChain:let W:=↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))
      let Z:=markedVortexNonDeeperHubType Vort 0
      let f:=markedVortexActiveVertexEmbedding Vort 1
      let g:=markedVortexNonDeeperHubToPhysical Vort 0
      let HL:=fun b v u=>Hraw b (f v) (g u)
      let HL':=fun b v u=>if b then Hraw true (f v) (g u) else Hnew false (f v) (g u)
      let FSactive:=markedSpokeChangeGraph HL HL';
    ∀(chain_k₀:ℕ),
    ∀(chain_α chain_ρ₀ chain_sstar chain_tstar chain_kstar:ℝ),
    ∀(chain_εAbs chain_ζAbs chain_βconfig chain_βCommon chain_εref chain_δref chain_tolRef chain_ζActive chain_τ chain_tolLocal chain_ζLocal chain_τParent chain_tolParent chain_ζParent chain_epsBal chain_ζBal chain_ζCut chain_ζCfg chain_rowErr chain_ζCommon chain_ζWide chain_ζRow:ℝ),
    ∀(chain_size chain_a₀ chain_b₀ chain_e₀ chain_f₀:ℕ),
    ∀(chain_s₀ chain_p chain_kval:ℝ),
    ∀(chain_q:U → Bool → ℝ),
    ∀(chain_s:U → Bool → ℝ),
    ∀(chain_weightParent:∀i,(Fin (r+4+1) → markedVortexVertexType Vort i) → ℝ),
    ∀(chain_weight:∀i,(Fin (r+4+1) → ↥((Finset.univ\markedVortexInnerVertices Vort i):Finset (markedVortexVertexType Vort i))) → ℝ),
    ∀(chain_βA chain_βrec chain_κ chain_ξ chain_thetaDeep chain_ω chain_xiDeep chain_etaBal chain_x chain_eta chain_deltaI chain_hIcut chain_αParent chain_κold chain_xold chain_thetaOld chain_etaOld:ℝ),
    ∀(chain_N chain_NI chain_Kgeom:ℕ),
    ∀(chain_hα:0<chain_α),
    ∀(chain_hαle:chain_α ≤ chain_αParent),
    ∀(chain_hκle:chain_κold ≤ chain_κ),
    ∀(chain_hxle:chain_xold ≤ chain_x),
    ∀(chain_hθle:chain_thetaOld ≤ chain_thetaDeep),
    ∀(chain_hηle:chain_etaOld ≤ chain_eta),
    ∀(chain_hρ:0  ≤  initialIndexDensity U Dv),
    ∀(chain_hs₀:0 ≤ chain_s₀),
    ∀(chain_hd:1 ≤ d),
    ∀(chain_he:0 ≤ ε),
    ∀(chain_hp:chain_p=initialIndexDensity U Dv*chain_s₀/2),
    ∀(chain_hk:chain_kval=chain_p/(((r+4):ℕ):ℝ)),
    ∀(chain_hq0:∀u,chain_q u false=chain_s₀/(((r+4):ℕ):ℝ)),
    ∀(chain_hs0:∀u,chain_s u false=chain_s₀),
    ∀(chain_hXi0:0 ≤ chain_xiDeep),
    ∀(chain_hXiScale:(4*chain_Kgeom+3*r+50:ℝ)*chain_xiDeep ≤ chain_κ/2),
    ∀(chain_hDeepGap:(1+2/initialIndexDensity U Dv)*chain_xiDeep ≤ (chain_s₀/(((r+4):ℕ):ℝ))*chain_ω/32),
    ∀(chain_hParentWeight:∀i ≤ L,SuccessorSequenceWeightConditions (P.comap (markedVortexVertexEmbedding Vort i))
      (markedVortexPermutation Vort π hπ i) (3*d) (2*(Fintype.card (markedVortexHubType Vort i):ℝ)/initialIndexDensity U Dv)
      chain_τParent (successorWeightLower chain_k₀ (chain_αParent/4)) (successorWeightUpper chain_k₀ (chain_αParent/4)) (chain_weightParent i)),
    ∀(chain_hActiveWeight:∀i ≤ L+1,SuccessorSequenceWeightConditions (P.comap (markedVortexActiveVertexEmbedding Vort i))
      (markedVortexActivePermutation Vort π hπ i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Vort i):Finset (markedVortexHubType Vort i)).card):ℝ)/initialIndexDensity U Dv)
      chain_τ (successorWeightLower chain_k₀ (chain_αParent/4)) (successorWeightUpper chain_k₀ (chain_αParent/4)) (chain_weight i)),
    ∀(chain_hGeo:MarkedVortexGeometricRecordEvent Vort chain_α chain_ρ₀ chain_κ chain_hIcut chain_ξ chain_xiDeep chain_ω chain_x chain_N chain_NI L),
    ∀(chain_hGood:MarkedVortexParentRecordSmallerReferenceEvent r (r+12) chain_k₀ d chain_αParent chain_ρ₀ chain_sstar chain_tstar chain_kstar
      chain_εAbs chain_ζAbs chain_βconfig chain_βCommon chain_εref chain_δref chain_tolRef chain_ζActive chain_τ chain_tolLocal chain_ζLocal chain_τParent chain_tolParent chain_ζParent chain_epsBal chain_ζBal chain_ζCut chain_ζCfg chain_rowErr chain_ζCommon chain_ζWide chain_ζRow
      chain_size chain_a₀ chain_b₀ chain_e₀ chain_f₀ P Dv mm β ε Vort π hπ L chain_s₀ chain_p chain_kval chain_q chain_s false false chain_weightParent chain_weight (markedExpandedActualSelected π d z)),
    ∀(chain_hβA:chain_βA ≤ chain_βCommon),
    ∀(chain_hζκ:chain_ζCommon ≤ chain_κold/4),
    ∀(chain_hC:3*chain_βA ≤ markedLocalCycleCoefficient r (chain_αParent/2) (chain_tstar/2) chain_kstar-(r+5:ℕ)*chain_ζCfg),
    ∀(chain_hP:3*chain_βA ≤ markedLocalPathCoefficient r (chain_αParent/2) (chain_tstar/2) chain_kstar-(r+4:ℕ)*chain_ζCfg),
    ∀(chain_hrec:chain_βrec ≤ chain_βA),
    ∀(chain_herr:chain_tolRef+(r+12:ℕ)*chain_ζActive ≤ chain_κold/4),
    ∀(chain_hζActiveK:chain_ζActive ≤ chain_κold/4),
    ∀(chain_hεeq:chain_εref ≤ chain_κold/4),
    ∀(chain_hδeq:chain_δref=chain_κold),
    ∀(chain_hpot:chain_τParent+chain_tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper chain_k₀ (chain_αParent/4)/(chain_ρ₀*chain_sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*chain_ζParent ≤ chain_κold/4),
    ∀(chain_hdeep:chain_τParent+chain_tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper chain_k₀ (chain_αParent/4)/(chain_ρ₀*chain_sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*chain_ζParent ≤ chain_thetaOld/4),
    ∀(chain_hxold:0 ≤ chain_xold),
    ∀(chain_hbal:chain_epsBal+((r+4)+2:ℕ)*chain_ζBal ≤ chain_etaBal),
    ∀(chain_hmargin:chain_epsBal+((r+4)+2:ℕ)*chain_ζBal ≤ chain_xold/2),
    ∀(chain_hterminal:L+1=Vort.length),
    ∀(chain_hrowmargin:chain_rowErr+chain_ζRow ≤ (chain_s₀/((r+4:ℕ):ℝ))/8),
    ∀(chain_hloadmargin:chain_τ+chain_tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper chain_k₀ (chain_αParent/4)/(chain_ρ₀*chain_sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*chain_ζWide ≤ chain_etaOld/4),
    ∀(chain_hbquarter:β ≤ 1/4),
    ∀(chain_hh:0 ≤ chain_hIcut),
    ∀(chain_hδα:chain_deltaI ≤ (chain_αParent/2)/32),
    ∀(chain_hδstar:chain_deltaI ≤ chain_kstar/32),
    ∀(chain_hδt:2*chain_deltaI ≤ chain_tstar/8),
    ∀(chain_hhstar:2*chain_hIcut ≤ (chain_αParent/2)*chain_kstar/4),
    ∀(chain_hhs:2*chain_hIcut ≤ chain_tstar/8-chain_ζCut),
    ∀(chain_hEndpoint:chain_tolRef+(r+12:ℕ)*chain_ζActive ≤ chain_xold/2),
    ∀(chain_iota:ℝ),
    ∀(chain_hηBalPos:0<chain_etaBal),
    ∀(chain_hxPos:0<chain_x),
    ∀(chain_hiota:0 < chain_iota),
    ∀(chain_hζchange:0 ≤ ζChange),
    ∀(chain_hepsBal:0 ≤ chain_epsBal),
    ∀(chain_hζBal:0 ≤ chain_ζBal),
    ∀(chain_hBalRelative:chain_epsBal+((r+4)+2:ℕ)*chain_ζBal ≤ chain_etaBal/2),
    ∀(chain_hBalAmbient:chain_epsBal+((r+4)+2:ℕ)*chain_ζBal ≤ chain_x/4),
    ∀(chain_hsize:chain_iota*Fintype.card (markedVortexVertexType Vort 0) ≤ ((markedVortexInnerVertices Vort 0).card:ℝ)),
    ∀(chain_hn:0<Fintype.card (Fin n)),
    ∀(chain_hu:Fintype.card U ≤ Fintype.card (Fin n)),
    ∀(chain_pstar:ℝ),
    ∀(chain_hpstar:0<chain_pstar),
    ∀(chain_hplo:chain_pstar ≤ chain_p),
    ∀(chain_hklo:chain_pstar ≤ chain_kval),
    ∀(chain_hslo:chain_pstar ≤ chain_s₀),
    ∀(chain_hp1:chain_p ≤ 1),
    ∀(chain_hk1:chain_kval ≤ 1),
    ∀(chain_hs1:chain_s₀ ≤ 1),
    ∀(chain_hDlo:(Fintype.card (markedVortexVertexType Vort 0):ℝ)/2 ≤ 2*(Fintype.card (markedVortexHubType Vort 0):ℝ)/initialIndexDensity U Dv),
    ∀(chain_hDhi:2*(Fintype.card (markedVortexHubType Vort 0):ℝ)/initialIndexDensity U Dv ≤ 2*Fintype.card (markedVortexVertexType Vort 0)),
    ∀(chain_hboundaryHalf:chain_xold ≤ chain_x/2),
    ∀(chain_hκPos:0<chain_κ),
    ∀(chain_hωPos:0<chain_ω),
    ∀(chain_plo chain_klo:ℝ),
    ∀(chain_hploPos:0<chain_plo),
    ∀(chain_hkloPos:0<chain_klo),
    ∀(chain_hαeq:chain_αParent=2*chain_α),
    ∀(chain_hκoldEq:chain_κold=chain_κ/2),
    ∀(chain_hUlower:chain_ω*Fintype.card (Fin n) ≤ (Fintype.card U:ℝ)),
    ∀(chain_hpLower:chain_plo ≤ chain_p),
    ∀(chain_hkLower:chain_klo ≤ chain_kval),
    ∀(chain_ζFixed:ℝ),
    ∀(chain_hζFixed:0<chain_ζFixed),
    ∀(chain_hCfg:2*chain_ζCfg ≤ chain_ζFixed),
    ∀(chain_hθDeepPos:0<chain_thetaDeep),
    ∀(chain_hθoldHalf:chain_thetaOld ≤ chain_thetaDeep/2),
    ∀(chain_hcycleDeep:3*chain_βA ≤ markedLocalCycleCoefficient r (chain_αParent/2) (chain_tstar/2) chain_kstar-(r+5:ℕ)*chain_ζFixed),
    ∀(chain_hpathDeep:3*chain_βA ≤ markedLocalPathCoefficient r (chain_αParent/2) (chain_tstar/2) chain_kstar-(r+4:ℕ)*chain_ζFixed),
    ∀(chain_hηPos:0<chain_eta),
    ∀(chain_htstarPos:0<chain_tstar),
    ∀(chain_hnactive:0<Fintype.card ↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))),
    ∀(chain_hβrect:chain_βrec ≤ (chain_s₀/((r+4:ℕ):ℝ))/4),
    ∀(chain_htt:chain_tstar ≤ chain_s₀/((r+4:ℕ):ℝ)),
    ∀(chain_hactiveErr:chain_τ+chain_tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper chain_k₀ (chain_αParent/4)/(chain_ρ₀*chain_sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*chain_ζWide ≤ chain_eta/8),
    ∀(chain_hactiveRow:chain_rowErr+chain_ζRow ≤ chain_tstar/16),
    ∀(chain_hDactiveLo:(Fintype.card ↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1)):ℝ)/2 ≤ 
      2*((((Finset.univ\markedVortexInnerHubs Vort 1):Finset (markedVortexHubType Vort 1)).card):ℝ)/initialIndexDensity U Dv),
    ∀(chain_hDactiveHi:2*((((Finset.univ\markedVortexInnerHubs Vort 1):Finset (markedVortexHubType Vort 1)).card):ℝ)/initialIndexDensity U Dv ≤ 
      2*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))),
    ∀(chain_hρ₀Pos:0<chain_ρ₀),
    ∀(chain_hρlo:chain_ρ₀ ≤ initialIndexDensity U Dv),
    ∀(chain_hρhi:initialIndexDensity U Dv ≤ 1),
    ∀(chain_htstarCap:chain_tstar ≤ (1/100)/(((r+4):ℕ):ℝ)),
    ∀(chain_hkstarPos:0<chain_kstar),
    ∀(chain_hkstarCap:chain_kstar ≤ initialIndexDensity U Dv*((1/100)/(((r+4):ℕ):ℝ))/2),
    ∀(chain_hs₀Eq:chain_s₀=(1/100:ℝ)),
    ∀(chain_hcLocalEq:cLocal=Classical.choose ((marked_vortex_initial_balance_from_parent_ambient_local_changes r chain_x chain_hxPos).2 chain_etaBal chain_hηBalPos)),
    ∀(chain_hζFinal:ζChange ≤ Classical.choose (marked_vortex_fixed_margin_local_correction_cap r chain_κ chain_αParent chain_ω chain_plo chain_klo chain_tstar chain_kstar chain_ζFixed chain_thetaDeep chain_eta
      (successorWeightUpper chain_k₀ (chain_αParent/4)) chain_pstar chain_etaBal chain_x chain_iota
      chain_hκPos (lt_of_lt_of_le chain_hα chain_hαle) chain_hωPos chain_hploPos chain_hkloPos chain_htstarPos chain_hζFixed chain_hθDeepPos chain_hηPos
      (successorWeightConstants_pos chain_k₀ (chain_αParent/4) (by have chain_hh:=lt_of_lt_of_le chain_hα chain_hαle;positivity)).2.le
      chain_hpstar chain_hηBalPos chain_hxPos chain_hiota)),
        (∀rho omega t:ℝ,chain_ρ₀ ≤ rho → rho ≤ 1 → chain_ρ₀/8 ≤ omega → omega ≤ 1 → chain_tstar ≤ t → (r+4:ℝ)*t ≤ 1 → 
      chain_ρ₀/400 ≤ rho*(r+4:ℝ)*t/2 → chain_kstar ≤ rho*(r+4:ℝ)*t/2 → chain_kstar ≤ rho*t/2 → chain_kstar ≤ t → 
      ∀(Gamma Shade:Type) [Fintype Gamma] [Fintype Shade],
      ∀level:MarkedReferenceLevelData Gamma Shade r d chain_N chain_NI chain_Kgeom (chain_α/16) rho omega t chain_kstar chain_βA
        (successorWeightLower chain_k₀ (chain_α/4)) (successorWeightUpper chain_k₀ (chain_α/4))
        chain_κ chain_ξ chain_thetaDeep (chain_α/8) chain_ω (ε/4) chain_βrec (successorWeightLower chain_k₀ (chain_α/4)) (successorWeightUpper chain_k₀ (chain_α/4))
        chain_eta chain_x (chain_ρ₀/16) chain_hIcut chain_deltaI chain_etaBal,
      MarkedReferenceLevelStepProperty level γLoss σLoss) → ε≤εStable → 2*mm≤sizeStable →
    ∀(hγ:0<γLoss) (hσ:0<σLoss),
    Classical.choose (marked_vortex_terminal_budget eStable γLoss σLoss hγ hσ)≤Fintype.card (Fin n) →
    let Earc:=MarkedSampleArc P π (3*d) (fun e=>τtarget (Sum.inl e)) false
    let Karc:=MarkedSampleArc P π (3*d) (fun e=>τtarget (Sum.inl e)) true;
    HasResourceDecomposition (fun W:MarkedWheel (fun e:Earc=>e.val.1) (fun e=>e.val.2)
      (fun e:Karc=>e.val.1) (fun e=>e.val.2) (r+4) π (3*d) (Hnew false) (Hnew true)=>markedWheelPhysicalResources W)
      (markedDecompositionTarget (markedPhysicalRimSet (fun e:Earc=>e.val.1) (fun e=>e.val.2)
        (fun e:Karc=>e.val.1) (fun e=>e.val.2) π) (Hnew false) (Hnew true)):=by
    intro W Z f g HL HL' FSactive
    intro chain_k₀ chain_α chain_ρ₀ chain_sstar chain_tstar chain_kstar chain_εAbs chain_ζAbs chain_βconfig chain_βCommon
      chain_εref chain_δref chain_tolRef chain_ζActive chain_τ chain_tolLocal chain_ζLocal chain_τParent chain_tolParent chain_ζParent
      chain_epsBal chain_ζBal chain_ζCut chain_ζCfg chain_rowErr chain_ζCommon chain_ζWide chain_ζRow chain_size chain_a₀
      chain_b₀ chain_e₀ chain_f₀ chain_s₀ chain_p chain_kval chain_q chain_s chain_weightParent chain_weight
      chain_βA chain_βrec chain_κ chain_ξ chain_thetaDeep chain_ω chain_xiDeep chain_etaBal chain_x chain_eta
      chain_deltaI chain_hIcut chain_αParent chain_κold chain_xold chain_thetaOld chain_etaOld chain_N chain_NI chain_Kgeom
      chain_hα chain_hαle chain_hκle chain_hxle chain_hθle chain_hηle chain_hρ chain_hs₀ chain_hd chain_he
      chain_hp chain_hk chain_hq0 chain_hs0 chain_hXi0 chain_hXiScale chain_hDeepGap chain_hParentWeight chain_hActiveWeight chain_hGeo
      chain_hGood chain_hβA chain_hζκ chain_hC chain_hP chain_hrec chain_herr chain_hζActiveK chain_hεeq chain_hδeq
      chain_hpot chain_hdeep chain_hxold chain_hbal chain_hmargin chain_hterminal chain_hrowmargin chain_hloadmargin chain_hbquarter chain_hh
      chain_hδα chain_hδstar chain_hδt chain_hhstar chain_hhs chain_hEndpoint chain_iota chain_hηBalPos chain_hxPos chain_hiota
      chain_hζchange chain_hepsBal chain_hζBal chain_hBalRelative chain_hBalAmbient chain_hsize chain_hn chain_hu chain_pstar chain_hpstar
      chain_hplo chain_hklo chain_hslo chain_hp1 chain_hk1 chain_hs1 chain_hDlo chain_hDhi chain_hboundaryHalf chain_hκPos
      chain_hωPos chain_plo chain_klo chain_hploPos chain_hkloPos chain_hαeq chain_hκoldEq chain_hUlower chain_hpLower chain_hkLower
      chain_ζFixed chain_hζFixed chain_hCfg chain_hθDeepPos chain_hθoldHalf chain_hcycleDeep chain_hpathDeep chain_hηPos chain_htstarPos chain_hnactive
      chain_hβrect chain_htt chain_hactiveErr chain_hactiveRow chain_hDactiveLo chain_hDactiveHi chain_hρ₀Pos chain_hρlo chain_hρhi chain_htstarCap
      chain_hkstarPos chain_hkstarCap chain_hs₀Eq chain_hcLocalEq chain_hζFinal hSteps hεstable hterminalSize hγ hσ hNB Earc Karc
    have hrawChain:σ=(markedExpandedActualSelected π d z).1:=by rfl
    have hspokesChain:Hraw=retainedRawMarkedSpokes π d (fun e=>(markedExpandedActualSelected π d z).1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>(markedExpandedActualSelected π d z).1 (Sum.inr e)) false))
      (markedExpandedActualSelected π d z).2 false false:=by rfl
    have hc:=marked_vortex_corrected_complete_from_matching_fields
      r chain_k₀ d chain_α chain_ρ₀ chain_sstar chain_tstar chain_kstar
      chain_εAbs chain_ζAbs chain_βconfig chain_βCommon chain_εref chain_δref chain_tolRef chain_ζActive
      chain_τ chain_tolLocal chain_ζLocal chain_τParent chain_tolParent chain_ζParent chain_epsBal chain_ζBal
      chain_ζCut chain_ζCfg chain_rowErr chain_ζCommon chain_ζWide chain_ζRow chain_size chain_a₀
      chain_b₀ chain_e₀ chain_f₀ P Dv mm β ε
      Vort π hπ L chain_s₀ chain_p chain_kval chain_q
      chain_s false false chain_weightParent chain_weight σ τtarget Hraw
      Hnew chain_βA chain_βrec chain_κ chain_ξ chain_thetaDeep chain_ω chain_xiDeep
      chain_etaBal chain_x chain_eta chain_deltaI chain_hIcut chain_αParent chain_κold chain_xold
      chain_thetaOld chain_etaOld chain_N chain_NI chain_Kgeom chain_hα chain_hαle chain_hκle
      chain_hxle chain_hθle chain_hηle chain_hρ chain_hs₀ chain_hd chain_he chain_hp
      chain_hk chain_hq0 chain_hs0 chain_hXi0 chain_hXiScale chain_hDeepGap chain_hParentWeight chain_hActiveWeight
      chain_hGeo (markedExpandedActualSelected π d z) hrawChain hspokesChain chain_hGood chain_hβA chain_hζκ chain_hC
      chain_hP chain_hrec chain_herr chain_hζActiveK chain_hεeq chain_hδeq chain_hpot chain_hdeep
      chain_hxold chain_hbal chain_hmargin chain_hterminal chain_hrowmargin chain_hloadmargin chain_hbquarter chain_hh
      chain_hδα chain_hδstar chain_hδt chain_hhstar chain_hhs chain_hEndpoint chain_iota ζChange
      chain_hηBalPos chain_hxPos chain_hiota chain_hζchange chain_hepsBal chain_hζBal chain_hBalRelative chain_hBalAmbient
      FR FS chain_hsize chain_hn chain_hu chain_pstar chain_hpstar chain_hplo
      chain_hklo chain_hslo chain_hp1 chain_hk1 chain_hs1 chain_hDlo chain_hDhi (fun v w=>v∈Spokes w\Y w)
      chain_hboundaryHalf chain_hκPos chain_hωPos chain_plo chain_klo chain_hploPos chain_hkloPos chain_hαeq
      chain_hκoldEq chain_hUlower chain_hpLower chain_hkLower chain_ζFixed chain_hζFixed chain_hCfg chain_hθDeepPos
      chain_hθoldHalf chain_hcycleDeep chain_hpathDeep chain_hηPos chain_htstarPos FSactive chain_hnactive chain_hβrect
      chain_htt chain_hactiveErr chain_hactiveRow chain_hDactiveLo chain_hDactiveHi chain_hρ₀Pos chain_hρlo chain_hρhi
      chain_htstarCap chain_hkstarPos chain_hkstarCap chain_hs₀Eq cLocal chain_hcLocalEq chain_hζFinal hPacked
    have hRes:=hc γLoss σLoss hSteps sizeStable aStable bStable eStable fStable εStable
      (by
        have hh:=hτdiv
        dsimp only [Hnew,Y,Bool.true_eq_false,if_true,Bool.false_eq_true,if_false] at hh ⊢
        convert hh using 1 <;> congr! 12 <;> first | rfl | exact Subsingleton.elim _ _)
      (by
        have hh:=hAbs
        convert hh using 1 <;> congr! 12 <;> first | rfl | exact Subsingleton.elim _ _)
      hreg hDv hεstable hterminalSize hγ hσ hNB
    convert hRes using 1 <;> congr! 12 <;> first | rfl | exact Subsingleton.elim _ _
  exact ⟨Mix,hdis,hinc,Pack,E,Spokes,T,hclose,hPack,hApprox,hNew,hSafe,hCount,hMark,hOrd,hInnerT,hReserveT,hType,hAgree,hDiv,A,hSmall,hA,hFactor,hSpoke,hLoss,hNoNew,⟨Old,⟨hAssign,hPackOld⟩,hTarget⟩,hFirst,hcloseLocal,hTypeLocal,hNewLocal,Cimage,hProtect,hImageLocal,τtarget,hτint,hτinner,hτactive,hτdeep,hτcode,hτdiv,FR,FS,hFRims,hFR,hFRlocal,hFSchange,hFS,hFSlocal,hactive,hSpokeSmall,hTypes,hSep,hAbs,hRlocal,hSloc',hNoNew',hLossLocal,hInterval,hRawInner,hOrdinary,hFRglobal,hActive,hPacked,hChain⟩
end Oberwolfach
