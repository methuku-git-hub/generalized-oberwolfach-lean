module

public import Oberwolfach.FirstVortexConcreteCommonBalancedActualChainInnerSumExplicitLevel

@[expose] public section
/-! Project the reserve, corrected host and class-matching witness produced
from one selected sample, retaining every displayed caller hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance sameSampleCorrectionMatchingFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) sameSampleCorrectionMatchingSix : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance sameSampleCorrectionMatchingArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem first_vortex_same_sample_correction_matching
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
        (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2
 :=by
  obtain ⟨N,hN⟩:=first_vortex_concrete_common_balanced_actual_chain_inner_sum_explicit_cap_separate_level α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
    hα hlam hε hδ hδ1 hθ hepsPos hρ₀ hbmatch hαb hbd hεsmall hθδ hθlocal hθhi hlamlocal hspacing hd hK hm heps hξ hξ0
    hρ₀hi hδglobal hθglobal hprecise ξCap hξPartCap hCap hlamθ hdlarge Nret hNret hrho heta hetaR hbudget hsupply
  refine ⟨N,?_⟩
  intro n hn _ U _ _ P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ ρ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z ζselect hζselect Inner βList terr τerr hτerr hEvent
  intro γLoss σLoss size a₀ b₀ e₀ f₀ L Bpart εAbs ζCorr ξCorr hsize hL hπ hξCorr hbudgetCorr heAbs heB hEvery hProtected hHost αAssign ρreserve hαAssign hReserveScale hee
  intro βfinal κ boundary loc lossInside inside δsmall ρsmall δspoke hU hεδ hβ hβ1 hδbound hn0 hnβ hnδ hu hκ hδsmall hθsmall hnsmall hρsmall hscale hbadsmall hδspoke hspokeScale hSharp hθκ hδstrong hnstrong hloc hinside hboundaryRate hlocGlobal hinsideGlobal hOuterNonneg hInsideBound hInsideBudget hlocalBudget hρreserve hListMargin hΔξ
  intro h hh sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon ρHost hρHost hsizeHost
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance hγRich levelWeight hCommon
    κaux κref hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hκauxRet
  intro εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable hstable
  have hc:=hN n hn
  obtain ⟨D₀,C,hTerminal,S,Mhost,Del,hSP,hregS,hEdit,hInner,hRes,hCover,hwitness,hPrepared,hRest⟩:=hc U P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ ρ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z ζselect hζselect Inner βList terr τerr hτerr hEvent
    γLoss σLoss size a₀ b₀ e₀ f₀ L Bpart εAbs ζCorr ξCorr hsize hL hπ hξCorr hbudgetCorr heAbs heB hEvery hProtected hHost αAssign ρreserve hαAssign hReserveScale hee
    βfinal κ boundary loc lossInside inside δsmall ρsmall δspoke hU hεδ hβ hβ1 hδbound hn0 hnβ hnδ hu hκ hδsmall hθsmall hnsmall hρsmall hscale hbadsmall hδspoke hspokeScale hSharp hθκ hδstrong hnstrong hloc hinside hboundaryRate hlocGlobal hinsideGlobal hOuterNonneg hInsideBound hInsideBudget hlocalBudget hρreserve hListMargin hΔξ
    h hh sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon ρHost hρHost hsizeHost βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance hγRich levelWeight hCommon κaux κref hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hκauxRet εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable hstable
  exact ⟨D₀,C,hTerminal,S,Mhost,Del,hSP,hregS,hEdit,hInner,hRes,hCover,hwitness,hPrepared⟩
end Oberwolfach
