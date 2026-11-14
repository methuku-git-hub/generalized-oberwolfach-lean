module

public import Oberwolfach.FirstVortexSelectorUniversalMatchingAtGeometryFullChainDefinition

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
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem first_vortex_selector_universal_matching_at_geometry_full_chain
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
    (ρreserve κaux εBalSelected ζBalSelected δParentSelected:ℝ)
    (γLevelSelected σLevelSelected κmaxSelected:ℝ)
    (κgeom hcutGeom ξGeom xiDeep ωGeom xGeom:ℝ) (NGeom NIGeom:ℕ)
    (hNGeom:1≤NGeom) (hαRef:0<αRef) (he8:εQ≤1/8) (heAlpha:εQ≤αRef/8)
    (hκgeom:0<κgeom) (heκ:εQ≤κgeom) (hecut:εQ≤hcutGeom) (heξ:4*εQ≤ξGeom) (hedeep:εQ^2≤xiDeep)
    (hωGeom:0≤ωGeom) (hωv:ωGeom≤εQ/8) (hωu:ωGeom≤ρ₀*εQ/64) (hxGeom:0<xGeom)
    (hSel:FirstVortexSelectorUniversalMatchingAtLevelFullChain r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall αHost rPart ζret hαHost hrPart hζret hεQHost
      K hK3 hm θ hθpos hθ htstarBound d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap α δold δlocal bmatch cLocal ρreserve κaux εBalSelected ζBalSelected δParentSelected γLevelSelected σLevelSelected κmaxSelected):
    FirstVortexSelectorUniversalMatchingAtGeometryFullChain r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall αHost rPart ζret hαHost hrPart hζret hεQHost
      K hK3 hm θ hθpos hθ htstarBound d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap α δold δlocal bmatch cLocal ρreserve κaux εBalSelected ζBalSelected δParentSelected γLevelSelected σLevelSelected κmaxSelected κgeom hcutGeom ξGeom xiDeep ωGeom xGeom NGeom NIGeom :=by
  obtain ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,hNum,
    eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,
    ε₀,ηEvent,hε₀,hε₀one,hηEvent,hprob,εExtra,hExtra,hExtraBound,h⟩:=hSel
  refine ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,hNum,
    eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,
    ε₀,ηEvent,hε₀,hε₀one,hηEvent,hprob,εExtra,hExtra,hExtraBound,?_⟩
  obtain ⟨gammaLoss,sigmaLoss,hGamma,hSigma,hGammaCap,hSigmaCap,hGammaOrd,
    ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap,hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax,hκaux,hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,
    χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,βmax,hβmax,hGeom⟩:=h
  refine ⟨gammaLoss,sigmaLoss,hGamma,hSigma,hGammaCap,hSigmaCap,hGammaOrd,
    ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap,hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax,hκaux,hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,
    χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,βmax,hβmax,?_⟩
  exact hGeom κgeom hcutGeom ξGeom xiDeep ωGeom xGeom NGeom NIGeom hNGeom hαRef he8 heAlpha hκgeom heκ hecut heξ hedeep hωGeom hωv hωu hxGeom
end Oberwolfach
