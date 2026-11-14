module

public import Oberwolfach.FirstVortexRepeatedSelectorAtGeometryBudgetDef
public import Oberwolfach.FirstVortexSelectorLeafOriginalStepsRepeatedFactor

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
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem first_vortex_repeated_selector_factor_decomposition_caller
    (r k₀ K d NI Kgeom NGeom:ℕ) (αRef ρ₀:ℝ) (hα:0<αRef) (hρ₀:0<ρ₀) (hρone:ρ₀≤1)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (hδAbs:0≤δAbs)
    (cap rhoGlobal etaGlobal δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal:ℝ)
    (ε:ℝ) (hε:0<ε) (hε1:ε<1/4) (hεAbs:ε≤εAbs) (hεRob:ε≤εRob)
    (hεsmall:ε≤min (((min αRef (1/2:ℝ)/2)/2)*(ρ₀/(800*((r+4:ℕ):ℝ)))) (1/(200*((r+4:ℕ):ℝ)))/128)
    (hεHost:ε≤(2*αRef)/100000) (hεStable:ε≤εStable)
    (ζret:ℝ) (hζret:0<ζret) (hK3:3≤K) (hm:7≤r+4)
    (θ:ℝ) (hθpos:0<θ) (hθ100:θ≤1/100)
    (htstar:1/(200*((r+4:ℕ):ℝ))≤(1/100)/(((r+4):ℕ):ℝ))
    (hd:2≤d) (cBoundary:ℝ) (hcBoundary:0<cBoundary) (hspacing:4/(d:ℝ)≤cBoundary)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (lam:ℝ) (hlam:0<lam) (hlamθ:lam≤θ) (ξCap:ℝ) (hξCap:0<ξCap)
    (α δold δlocal bmatch ρreserve κaux:ℝ)
    (εSelected ζSelected δSelected γLevel σLevel:ℝ) (hγ:0<γLevel) (hσ:0<σLevel)
    (κ hIcut ξ xiDeep ω x thetaDeep etaBal etaLevel deltaI:ℝ) (hNGeom:1≤NGeom)
    (hκ:0<κ) (hx:0<x) (hθDeep:0<thetaDeep) (heta:0<etaLevel) (hEtaBal:0<etaBal)
    (hxi0:0≤xiDeep) (hXiScale:(4*(Kgeom:ℝ)+((3*r+50:ℕ):ℝ))*xiDeep≤κ/2)
    (hDeepSource:∀ρ t:ℝ,ρ₀≤ρ→1/(200*((r+4:ℕ):ℝ))≤t→(1+2/ρ)*xiDeep≤t*ω/32)
    (δbase ζFixed ζCut cap₁ cap₂ βA βrec:ℝ) (hζFixed:0<ζFixed)
    (hAt:FirstVortexActualParentAlignedAt r ρ₀ (1/100) (1/(200*((r+4:ℕ):ℝ)))
      (successorWeightUpper k₀ ((2*αRef)/4)) δbase ζFixed κ x thetaDeep etaLevel ε etaBal cap₁ cap₂ βA
      (markedLocalCycleCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ))))
      (markedLocalPathCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ)))) δSelected εSelected ζSelected)
    (hβA:βA≤βCommonP) (hrec:βrec≤βA) (hIcut0:0≤hIcut)
    (hδAlpha:deltaI≤αRef/32) (hδStar:deltaI≤(ρ₀/(800*((r+4:ℕ):ℝ)))/32)
    (hδTime:2*deltaI≤(1/(200*((r+4:ℕ):ℝ)))/8)
    (hIStar:2*hIcut≤αRef*(ρ₀/(800*((r+4:ℕ):ℝ)))/4)
    (hδbaseCut:δbase≤ζCut) (hCut:2*hIcut≤(1/(200*((r+4:ℕ):ℝ)))/8-ζCut)
    (hCycleFixed:3*βA≤markedLocalCycleCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ)))-(r+5:ℕ)*ζFixed)
    (hPathFixed:3*βA≤markedLocalPathCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ)))-(r+4:ℕ)*ζFixed)
    (hβrecT:βrec≤(1/(200*((r+4:ℕ):ℝ)))/4)
    (hActiveCap:active≤Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r (2*αRef)
      (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) ζFixed etaLevel
      (successorWeightUpper k₀ ((2*αRef)/4)) (ρ₀/(800*((r+4:ℕ):ℝ))) hζFixed heta
      (successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2.le (by positivity) (by positivity)))
    (s c ζlocal:ℝ) (hret:FirstVortexRetentionBalanceRates r d ε active θ s c ζret ζlocal ηBalance κaux)
    (hactive:0<active) (hcap:0<cap) (hcapStable:cap≤capStable)
    (hactiveGlobal:active≤(min cap (1:ℝ))/2)
    (hactiveLocal:active≤markedExplicitJointLocalCap (r+4) (r+12) etaBal x)
    (hChosen:FirstVortexExactParentCapBound r αRef ρ₀ κ ζFixed thetaDeep (successorWeightUpper k₀ ((2*αRef)/4)) cap hα hρ₀)
    (γCore σCore extra:ℝ) (hγSplit:γCore+extra=γLevel) (hσSplit:σCore+extra=σLevel)
    (hSteps:(∀rho omega t:ℝ,(ρ₀) ≤ rho → rho ≤ 1 → (ρ₀)/8 ≤ omega → omega ≤ 1 → ((1/(200*((r+4:ℕ):ℝ)))) ≤ t → (r+4:ℝ)*t ≤ 1 → 
      (ρ₀)/400 ≤ rho*(r+4:ℝ)*t/2 → ((ρ₀/(800*((r+4:ℕ):ℝ)))) ≤ rho*(r+4:ℝ)*t/2 → ((ρ₀/(800*((r+4:ℕ):ℝ)))) ≤ rho*t/2 → ((ρ₀/(800*((r+4:ℕ):ℝ)))) ≤ t → 
      ∀(Gamma Shade:Type) [Fintype Gamma] [Fintype Shade],
      ∀level:MarkedReferenceLevelData Gamma Shade r d NGeom (NI) (Kgeom) ((αRef)/16) rho omega t ((ρ₀/(800*((r+4:ℕ):ℝ)))) (βA)
        (successorWeightLower (k₀) ((αRef)/4)) (successorWeightUpper (k₀) ((αRef)/4))
        (κ) (ξ) (thetaDeep) ((αRef)/8) (ω) (ε/4) (βrec) (successorWeightLower (k₀) ((αRef)/4)) (successorWeightUpper (k₀) ((αRef)/4))
        (etaLevel) (x) ((ρ₀)/16) (hIcut) (deltaI) (etaBal),
      MarkedReferenceLevelStepProperty level (γCore+extra) (σCore+extra)))
    (hεcap:ε≤((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/32)
    (htrim:1/(100*((r+4:ℕ):ℝ))≤((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/16)
    (A:ℝ) (hHostGeom:HostMatchingVortexContinuation (r+4) K d (2*αRef) A BM BO)
    (hSel:FirstVortexRepeatedSelectorAtGeometryBudget r (r+12) k₀ 1 αRef (1/100) (ρ₀/4) (min αRef (1/2:ℝ)/2)
      (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap rhoGlobal etaGlobal δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal
      ε hε hε1 hεAbs hεRob hεsmall (2*αRef) 1 ζret (by positivity) (by norm_num) hζret hεHost
      K hK3 hm θ hθpos hθ100 htstar d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap
      α δold δlocal bmatch (markedExplicitJointLocalCap (r+4) (r+12) etaBal x) ρreserve κaux
      εSelected ζSelected δSelected γLevel σLevel (κ/2) hγ hσ κ hIcut ξ xiDeep ω x NGeom NI hα hρone):
    ∃N:ℕ,∀n≥N,∀(G:SimpleGraph (Fin n)) (D:ℕ),G.IsRegularOfDegree D→Even D→
      ∀F₀:SimpleGraph (Fin n),F₀.IsRegularOfDegree 2→∀Allowed:Set ℕ,
      Allowed.Nonempty→(∀s∈Allowed,3≤s)→AllowedCycleLengths F₀ Allowed→factorPreparationClass F₀ K=none→
      (allowedThreshold Allowed+2*αRef)*n≤(D:ℝ)→
      HasFactorDecomposition G (fun _:Fin (D/2)=>F₀) :=by
  obtain ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,hNum,
    eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγInner,hγBound,
    ε₀,ηEvent,hε₀,hε₀one,hηEvent,hprob,εExtra,hExtra,hExtraBound,h⟩:=hSel
  obtain ⟨gammaLoss,sigmaLoss,hGamma,hSigma,hGammaCap,hSigmaCap,hGammaOrd,
    ζCorr,ξCorr,η₀,κsel,εRef,εNbr,hζCorr,hζRob,hζCap,hξCorr,hξCorrRate,hbudget,
    hη₀,hκsel,hκmax,hκaux,hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,
    χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,βmax,hβmax,hGeom⟩:=h
  obtain ⟨βQ,hβQ,hβquarter,hβα4,hβmax',hβbal,hβref,MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξinner,ht₀,hτ₀,hτ₀cap,hΔ,hξinner,hξrate,
    mGeom,hmGeom,vsize,hvsize,hmLevelSize,hmGeomSize,τHost,hτHost,hτHostBound,NHostGeom,hNHostGeom,hHostLate,
    ξResidual,hξResidual,hξResidualBound,hζOrdResidual,hξResidualBound2,hξSeedResidual,hResidualScales,
    ζList,hζList,hζListCap,Nbase,a₀,b₀,e₀,aRob,bRob,eRob,aParent,bParent,eParent,aStable,bStable,eStable,Nchain,hChain,hSelect⟩:=hGeom A hHostGeom
  obtain ⟨NHost,hHostGeom,hChainOrder,hExtraOrder,hReserveHost,hBudgetHost,hHost⟩:=hSelect 0 0
  refine ⟨max (max Nbase NHost) 1,?_⟩
  intro n hn G D hreg hEven F₀ hF₀ Allowed hAllowedNonempty hAllowedValid hFAllowed hLong hmin
  have hnpos:0<n:=by omega
  letI:Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
  have hHostOut:=hHost n hn G D hreg hEven F₀ hF₀ Allowed hAllowedNonempty hAllowedValid hFAllowed hLong hmin (le_refl _) hδAbs hεcap htrim
  obtain ⟨Q,π,hpres,w,weight,hD,hsize,hnoshort,hU,hDpos,hDlo,hDhi,hmargin,hv,hGeo,hw0,hwupper,hedges,hbudgetV,hbudgetE,hwK,hRest⟩:=hHostOut
  obtain ⟨weightParent,weightActive,hParentWeight,hActiveWeight,levelWeight,hLevelWeight,z,hMass,hPrior,hParent,hExpanded,hStableEvent,hProtected,hEvery,hBoundary,hBound,hMatch⟩:=hRest
  have hGeoL:=hGeo (Q.length-1) (by have hh:=Q.length_pos; omega)
  have hnHost:NHost≤n:=by omega
  have hOneN:∀j:ℕ,1≤j→1≤(fun _=>NGeom) j:=by intro j hj; exact hNGeom
  have hθ1:θ≤1:=by linarith
  have hK:0<K:=by omega
  have hmm:0<vsize:=by omega
  refine first_vortex_selector_leaf_original_steps_repeated_factor (K:=K) hEven hDpos G π d r vsize βQ ε Q hpres active εStable eStable F₀ hF₀ θ hreg
    k₀ NI Kgeom aParent bParent eParent (fun _=>NGeom) hOneN
    αRef ρ₀ δSelected εSelected ζSelected εAbsP ζAbsP βconfigP βCommonP εRef
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x etaLevel deltaI hIcut
    hα hρ₀ hρone hκ hx hθDeep heta hd hε hxi0 hXiScale htstar hDeepSource
    δbase ζFixed ζCut cap₁ cap₂ hAt hβA hrec hεRefMax hβquarter hIcut0 hEtaBal hδAlpha hδStar hδTime hIStar hδbaseCut hCut
    hnpos hDlo hζFixed hCycleFixed hPathFixed hβrecT hActiveCap hd hnoshort
    (min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))) (min (epsOrd/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))) epsOrd ζOrd
    ((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)
    lamAssign δlocal δglobal α bmatch ξResidual weight w a₀ b₀ e₀ aRob bRob eRob 0 1
    β βCommon εAbs εRob ζRob εRef ζret εNbr 1 (successorWeightUpper k₀ ((2*αRef)/4)) 1 1 1 1 1
    hK hθpos.le hθ1 hγOrd.le hε1.le hmm s c ζret ζlocal ηBalance κaux cap capStable hret hactive hcap hcapStable hactiveGlobal hactiveLocal hChosen
    ξClassOrd gammaLoss sigmaLoss rhoGlobal etaGlobal κPack hεHost γLevel σLevel hγ hσ γCore σCore extra hγSplit hσSplit NHost hBudgetHost hnHost ?_ hSteps hεStable
  refine ⟨weightParent,weightActive,levelWeight,z,hParentWeight,hActiveWeight,hGeoL,hPrior,hParent,?_⟩
  exact ⟨hExpanded,hMatch⟩
end Oberwolfach
