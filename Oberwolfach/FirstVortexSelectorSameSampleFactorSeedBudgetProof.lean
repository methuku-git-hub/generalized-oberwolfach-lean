module

public import Oberwolfach.FirstVortexSelectorSameSampleFactorSeedBudgetDef

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem first_vortex_selector_same_sample_factor_seed_budget
    (r h k₀ Qpow:ℕ) (αRef sstar ω γRich tstar kstar ρ₀:ℝ) (hρ₀:0<ρ₀)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal:ℝ)
    (εQ:ℝ) (hεQ:0<εQ) (hεQ1:εQ<1/4) (hεQAbs:εQ≤εAbs) (hεQRob:εQ≤εRob)
      (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128)
    (αHost rPart ζret:ℝ) (hαHost:0<αHost) (hrPart:0<rPart) (hζret:0<ζret)
      (hεQHost:εQ≤αHost/100000)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ:ℝ) (hθpos:0<θ) (hθ:θ≤1/100)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (d:ℕ) (hd:2≤d) (cBoundary:ℝ) (hcBoundary:0<cBoundary) (hspacing:4/(d:ℝ)≤cBoundary) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (lam:ℝ) (hlam:0<lam) (hlamθ:lam≤θ) (ξCap:ℝ) (hξCap:0<ξCap)
    (α δold δlocal bmatch cLocal:ℝ)
    (ρreserve κaux:ℝ) (hκaux:0<κaux)
    (hReserveSize:∀e:ℕ,∃N:ℕ,∀n:ℕ,N≤n→(e:ℝ)≤ρreserve*n)
    (hSel:FirstVortexSelectorWithSameSampleFactorSeed r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall αHost rPart ζret hαHost hrPart hζret hεQHost
      K hK3 hm θ hθpos hθ htstarBound d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap α δold δlocal bmatch cLocal ρreserve κaux):
    FirstVortexSelectorSameSampleFactorSeedBudget r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall αHost rPart ζret hαHost hrPart hζret hεQHost
      K hK3 hm θ hθpos hθ htstarBound d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap α δold δlocal bmatch cLocal ρreserve κaux :=by
  obtain ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,hNum,
    eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,
    ε₀,ηEvent,hε₀,hε₀one,hηEvent,hprob,εExtra,hExtra,hExtraBound,hh⟩:=hSel
  refine ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,hNum,
    eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,
    ε₀,ηEvent,hε₀,hε₀one,hηEvent,hprob,εExtra,hExtra,hExtraBound,?_⟩
  intro γLevel σLevel κmax hγLevel hσLevel hκmax
  obtain ⟨gammaLoss,sigmaLoss,hGamma,hSigma,hGammaCap,hSigmaCap,hGammaOrd,
    ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap',hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,
    χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,hh⟩:=
    hh γLevel σLevel κmax κaux ζret hγLevel hσLevel hκmax hκaux hζret
  refine ⟨gammaLoss,sigmaLoss,hGamma,hSigma,hGammaCap,hSigmaCap,hGammaOrd,
    ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap',hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,
    χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,?_⟩
  intro εBal ζBal hεBal hζBal
  have hh:=hh ζret εBal ζBal hζret hεBal hζBal
  dsimp only []
  intro δparent hδparent
  obtain ⟨βmax,hβmax,hGeom⟩:=hh δparent hδparent
  refine ⟨βmax,hβmax,?_⟩
  intro κgeom hcutGeom ξGeom xiDeep ωGeom xGeom NGeom NIGeom hNGeom hαRef he8 heAlpha hκgeom heκ hecut heξ hedeep hωGeom hωv hωu hxGeom A hHostGeom
  obtain ⟨βQ,hβQ,hβquarter,hβα4,hβmax',hβbal,hβref,MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀cap,hΔ,hξ,hξrate,
    mGeom,hmGeom,vsize,hvsize,hmLevelSize,hmGeomSize,τHost,hτHost,hτHostBound,NHostGeom,hNHostGeom,hHostLate,
    ξResidual,hξResidual,hξResidualBound,hζOrdResidual,hξResidualBound2,hξSeedResidual,hResidualScales,
    ζList,hζList,hζListCap,N,a₀,b₀,e₀,aRob,bRob,eRob,aParent,bParent,eParent,aStable,bStable,eStable,Nchain,hChain,hSelect⟩:=
      hGeom κgeom hcutGeom ξGeom xiDeep ωGeom xGeom NGeom NIGeom hNGeom hαRef he8 heAlpha hκgeom heκ hecut heξ hedeep hωGeom hωv hωu hxGeom A hHostGeom
  refine ⟨βQ,hβQ,hβquarter,hβα4,hβmax',hβbal,hβref,MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀cap,hΔ,hξ,hξrate,
    mGeom,hmGeom,vsize,hvsize,hmLevelSize,hmGeomSize,τHost,hτHost,hτHostBound,NHostGeom,hNHostGeom,hHostLate,
    ξResidual,hξResidual,hξResidualBound,hζOrdResidual,hξResidualBound2,hξSeedResidual,hResidualScales,
    ζList,hζList,hζListCap,N,a₀,b₀,e₀,aRob,bRob,eRob,aParent,bParent,eParent,aStable,bStable,eStable,Nchain,hChain,?_⟩
  intro f₀ Nextra
  obtain ⟨Nreserve,hReserve⟩:=hReserveSize eRob
  obtain ⟨NHost,hHostGeom,hChainOrder,hExtraOrder,hHost⟩:=hSelect f₀ (max Nextra (max Nreserve (Classical.choose (marked_vortex_terminal_budget eStable γLevel σLevel hγLevel hσLevel))))
  have hNextra:Nextra≤NHost:=(le_max_left _ _).trans hExtraOrder
  have hReserveHost:∀n:ℕ,NHost≤n→(eRob:ℝ)≤ρreserve*n:=by
    intro n hn
    exact hReserve n ((le_max_left _ _).trans ((le_max_right _ _).trans (hExtraOrder.trans hn)))
  have hBudgetHost:Classical.choose (marked_vortex_terminal_budget eStable γLevel σLevel hγLevel hσLevel)≤NHost :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hExtraOrder)
  refine ⟨NHost,hHostGeom,hChainOrder,hNextra,hReserveHost,hBudgetHost,?_⟩
  intro n hn U _ _ F hF Allowed hAllowed hAllowedNonempty hAllowedValid hclass G Dnat hreg hmin hρlo hρ1 hEven hαHostLe hδAbs hεQcap htrim hk₁ hk₂ Itype _ density iclass hdensity hsum hparts hiclass hρeq
  obtain ⟨Q,π,hpres,w,weight,hD,hsize,hnoshort,hU,hDnat,hDlo,hDhi,hmargin,hv,hGeo,hw0,hwupper,hedges,hbudgetV,hbudgetE,hwK,hRest⟩:=
    hHost n hn U F hF Allowed hAllowed hAllowedNonempty hAllowedValid hclass G Dnat hreg hmin hρlo hρ1 hEven hαHostLe hδAbs hεQcap htrim hk₁ hk₂ Itype density iclass hdensity hsum hparts hiclass hρeq
  refine ⟨Q,π,hpres,w,weight,hD,hsize,hnoshort,hU,hDnat,hDlo,hDhi,hmargin,hv,hGeo,hw0,hwupper,hedges,hbudgetV,hbudgetE,hwK,?_⟩
  obtain ⟨weightParent,weightActive,hParentWeight,hActiveWeight,levelWeight,hLevelWeight,z,hMass,hPrior,hParent,hExpanded,hStable,hProtected,hEvery,hBoundary,hBound,hMatch⟩:=hRest
  refine ⟨weightParent,weightActive,hParentWeight,hActiveWeight,levelWeight,hLevelWeight,z,hMass,hPrior,hParent,hExpanded,hStable,hProtected,hEvery,hBoundary,hBound,?_⟩
  exact hMatch (hReserveHost n (by omega)) (le_refl _) (le_refl _)
end Oberwolfach
