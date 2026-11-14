module

public import Oberwolfach.FirstVortexFixedTerminalChainAtSelectedSample
public import Oberwolfach.FirstVortexNamedLevelChainContinuation
public import Oberwolfach.FirstVortexChainAtSelectedSample
public import Oberwolfach.FirstVortexSameSampleFixedClassChainNamedThreshold

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance fixedTerminalChainFactorSeedFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) fixedTerminalChainFactorSeedSix : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance fixedTerminalChainFactorSeedArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

def FirstVortexFixedTerminalChainFactorSeedAtSelectedSample
    (α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret:ℝ) (d K r:ℕ) (Δ rho δLoss εInner eta:ℝ) (e:ℕ)
    (cap cLocal active ηBalance κPack βfinal:ℝ) (N:ℕ):Prop :=
    ∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
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
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Parent:MarkedExpandedActualOutcome (U:=U) π d→Prop) (hParent:Parent z) (ζselect:ℝ) (hζselect:ζselect≤ζret) (Inner:Finset (Fin n)) (βList:ℝ)
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
    0<Fintype.card U → ε≤δglobal → Fintype.card U≤n →
    0≤ρreserve → βfinal+2*ρreserve≤βList/2 → Δ≤ξ →
    ∀(h:ℕ),1≤h→∀(sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon:ℕ)
      (ρHost:ℝ),0<ρHost→ρHost*Dv=2*Fintype.card U→
    ∀(βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
      εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀Event sstarEvent kstarEvent τLevelEvent:ℝ),0≤γRich→
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
    Parent z ∧ ∃boundary lossInside inside loc:ℝ,
      boundary=4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ) ∧
      FirstVortexSummedLossAt n d ((markedVortexInnerVertices Vort 0).card:ℝ)
        cLocal rho eta θ a γ ξPart κPack Δ ζret ηBalance boundary lossInside inside loc ∧
    let κ:=κPack
    let δsmall:=δglobal
    let ρsmall:=θ/4096
    let δspoke:=δglobal;
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
    0<K→θ≤1→∀ζRet:ℝ,
    0<active→0<ε→ε≤1/4→0<mm→0≤ζRet→ζRet≤active/128→ζret≤ζRet*ε/2→
    ∀p₂ k₂ u:ℝ,
    (∀v,|((rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K (r+4) θ w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
    (∀j v,|((∑x,sampledColourOrientation P (fun x=>z.1 (Sum.inl x)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability (initialIndexDensity U Dv*(1/100:ℝ)/2) (initialIndexDensity U Dv*((1/100:ℝ)/((r+4:ℕ):ℝ))/2) p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ))→
    0≤γ→0≤θ→u≤2*θ→
    (∀v,|((sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) 4 v):ℝ)-u*(P.degree v:ℝ)|≤(n:ℝ)^(3/5:ℝ))→
    ∀(ζChange:ℝ),0≤ζChange→ζChange≤capStable→
    active≤ζChange→(min cap (1:ℝ))/2≤ζChange→0≤cLocal→active≤cLocal→
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let Hraw:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false false;
    ∃(Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))) (Spokes:U→Finset (Fin n))
      (A:Finset (Fin n×Fin n)),
      let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E;
      Small.edgeFinset=A.image (fun a=>s(a.1,a.2)) ∧
      LongFactorComplementProvenance F S P π d (r+4) raw t z.2 Pack E A Spokes ∧
      ∃T:Finset {a:Fin n×Fin n // longEligibleResidualArc Mhost Small ⊥ a},
      ∃τnew:RawMarkedOutcome (Fin n) U Bool Bool,
      (∀mark x y,markedPhysicalRim P π (3*d) (fun e=>τnew (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc (longEligibleResidualArc Mhost Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc (longEligibleResidualArc Mhost Small ⊥) T,e.val.val.1=x∧e.val.val.2=y) ∧
      let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun x=>raw (Sum.inr x)) false t z.2 w=>d) Subtype.val
      let Hnew:Bool→Fin n→U→Prop:=fun b v w=>if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false true true v w else v∈Spokes w\Y w;
      FirstVortexNamedLevelChainContinuation P π d r Dv mm β ε Vort hπ L z τnew Hnew active cLocal ζChange εStable sizeStable eStable

theorem first_vortex_fixed_terminal_chain_factor_seed_at_selected_sample
    (α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret:ℝ) (d K r:ℕ) (Δ rho δLoss εInner eta:ℝ) (e:ℕ)
    (cap cLocal active ηBalance κPack βfinal:ℝ) (N:ℕ)
    (hChain:FirstVortexFixedTerminalChainAtSelectedSample α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
      cap cLocal active ηBalance κPack βfinal N):
    FirstVortexFixedTerminalChainFactorSeedAtSelectedSample α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
      cap cLocal active ηBalance κPack βfinal N :=by
  intro n hn _ U _ _ P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ ρ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z Parent hParent ζselect hζselect Inner βList terr τerr hτerr hEvent
  intro γLoss σLoss size a₀ b₀ e₀ f₀ L Bpart εAbs ζCorr ξCorr hsize hL hπ hξCorr hbudgetCorr heAbs heB hEvery hProtected Chain Dsel Csel hTerminal hChainSelected hPreparedClasses αAssign ρreserve hαAssign hReserveScale hee
  intro hU hεδ hu hρreserve hListMargin hΔξ
  intro h hh sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon ρHost hρHost hsizeHost
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent hγRich levelWeight hCommon
    κaux κref hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hκauxRet
  intro εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable hstable
  have hold := hChain n hn U P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ ρ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z Parent hParent ζselect hζselect Inner βList terr τerr hτerr hEvent
    γLoss σLoss size a₀ b₀ e₀ f₀ L Bpart εAbs ζCorr ξCorr hsize hL hπ hξCorr hbudgetCorr heAbs heB hEvery hProtected Chain Dsel Csel hTerminal hChainSelected hPreparedClasses αAssign ρreserve hαAssign hReserveScale hee
    hU hεδ hu hρreserve hListMargin hΔξ
    h hh sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon ρHost hρHost hsizeHost
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent hγRich levelWeight hCommon
    κaux κref hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hκauxRet εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable hstable
  obtain ⟨hParent',boundary,lossInside,inside,loc,hboundary,hSum,⟨hTermOut,hChainOut⟩,hFor⟩:=hold
  refine ⟨hParent',boundary,lossInside,inside,loc,hboundary,hSum,⟨hTermOut,hChainOut⟩,?_⟩
  intro S hSP hRegS hEditS hInnerS hReserveS
  obtain ⟨Mhost,Del,hSP',hRegS',hEditS',hInnerS',hReserveS',hCover,hWitness,hPrepared,hContinuation⟩:=
    hFor S hSP hRegS hEditS hInnerS hReserveS
  refine ⟨Mhost,Del,hSP',hRegS',hEditS',hInnerS',hReserveS',hCover,hWitness,hPrepared,?_⟩
  dsimp only []
  intro hK hθ ζRet hactive hε hε1 hmm' hζRet0 hζRetCap hζRate p₂ k₂ u hStart hOrient hγ hθ0 hu hColour ζChange hζChange0 hζChangeCap hactiveChange hminChange hcLocal hactiveLocal
  have hwitness:=hContinuation hK hθ ζRet hactive hε hε1 hmm' hζRet0 hζRetCap hζRate p₂ k₂ u hStart hOrient hγ hθ0 hu hColour ζChange hζChange0 hζChangeCap hactiveChange hminChange hcLocal hactiveLocal
  obtain ⟨Mix,hdisj,hinc,Pack,E,Spokes,T,hbody⟩:=hwitness
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,A,hSmall,_,hprov,_,_,_,_,_,_,_,_,Cimage,_,_,τnew,_,_,_,_,hcode,_,FR,FS,hrest⟩:=hbody
  refine ⟨Pack,E,Spokes,A,hSmall,hprov,T,τnew,hcode,?_⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hNext⟩:=hrest
  exact hNext
end Oberwolfach
