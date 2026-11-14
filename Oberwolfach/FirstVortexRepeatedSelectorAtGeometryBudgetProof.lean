module

public import Oberwolfach.FirstVortexRepeatedSelectorAtGeometryBudgetDef
public import Oberwolfach.FirstVortexSelectorUniversalMatchingAtGeometryFactorSeed
public import Oberwolfach.RepeatedFactorOriginalSelectorInputs
public import Oberwolfach.FirstVortexSelectorUniversalMatchingAtGeometry
public import Oberwolfach.FirstVortexSelectorUniversalMatchingAtLevelFactorSeed

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

theorem first_vortex_repeated_selector_at_geometry_budget
    (r h k₀ Qpow:ℕ) (αRef sstar ω γRich tstar kstar ρ₀:ℝ) (hρ₀:0<ρ₀)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal:ℝ)
    (εQ:ℝ) (hεQ:0<εQ) (hεQ1:εQ<1/4) (hεQAbs:εQ≤εAbs) (hεQRob:εQ≤εRob)
      (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128)
    (αHost rPart ζret:ℝ) (hαHost:0<αHost) (hrPart:0<rPart) (hrPartOne:rPart≤1) (hζret:0<ζret)
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
    (hγLevel:0<γLevelSelected) (hσLevel:0<σLevelSelected)
    (κgeom hcutGeom ξGeom xiDeep ωGeom xGeom:ℝ) (NGeom NIGeom:ℕ)
    (hNGeom:1≤NGeom) (hαRef:0<αRef) (hρone:ρ₀≤1) (hkstar:kstar=ρ₀/(800*((r+4:ℕ):ℝ))) (he8:εQ≤1/8) (heAlpha:εQ≤αRef/8)
    (hκgeom:0<κgeom) (heκ:εQ≤κgeom) (hecut:εQ≤hcutGeom) (heξ:4*εQ≤ξGeom) (hedeep:εQ^2≤xiDeep)
    (hωGeom:0≤ωGeom) (hωv:ωGeom≤εQ/8) (hωu:ωGeom≤ρ₀*εQ/64) (hxGeom:0<xGeom)
    (hSel:FirstVortexSelectorUniversalMatchingAtGeometryBudgetFactorSeed r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall αHost rPart ζret hαHost hrPart hζret hεQHost
      K hK3 hm θ hθpos hθ htstarBound d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap α δold δlocal bmatch cLocal ρreserve κaux εBalSelected ζBalSelected δParentSelected γLevelSelected σLevelSelected κmaxSelected hγLevel hσLevel κgeom hcutGeom ξGeom xiDeep ωGeom xGeom NGeom NIGeom):
    FirstVortexRepeatedSelectorAtGeometryBudget r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall αHost rPart ζret hαHost hrPart hζret hεQHost
      K hK3 hm θ hθpos hθ htstarBound d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap α δold δlocal bmatch cLocal ρreserve κaux εBalSelected ζBalSelected δParentSelected γLevelSelected σLevelSelected κmaxSelected hγLevel hσLevel κgeom hcutGeom ξGeom xiDeep ωGeom xGeom NGeom NIGeom hαRef hρone :=by
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
  intro A hHostGeom
  obtain ⟨βQ,hβQ,hβquarter,hβα4,hβmax',hβbal,hβref,MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀cap,hΔ,hξ,hξrate,
    mGeom,hmGeom,vsize,hvsize,hmLevelSize,hmGeomSize,τHost,hτHost,hτHostBound,NHostGeom,hNHostGeom,hHostLate,
    ξResidual,hξResidual,hξResidualBound,hζOrdResidual,hξResidualBound2,hξSeedResidual,hResidualScales,
    ζList,hζList,hζListCap,N,a₀,b₀,e₀,aRob,bRob,eRob,aParent,bParent,eParent,aStable,bStable,eStable,Nchain,hChain,hSelect⟩:=hGeom A hHostGeom
  refine ⟨βQ,hβQ,hβquarter,hβα4,hβmax',hβbal,hβref,MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀cap,hΔ,hξ,hξrate,
    mGeom,hmGeom,vsize,hvsize,hmLevelSize,hmGeomSize,τHost,hτHost,hτHostBound,NHostGeom,hNHostGeom,hHostLate,
    ξResidual,hξResidual,hξResidualBound,hζOrdResidual,hξResidualBound2,hξSeedResidual,hResidualScales,
    ζList,hζList,hζListCap,N,a₀,b₀,e₀,aRob,bRob,eRob,aParent,bParent,eParent,aStable,bStable,eStable,Nchain,hChain,?_⟩
  intro f₀ Nextra
  obtain ⟨NHost,hHostGeom,hChainOrder,hExtraOrder,hReserveHost,hBudgetHost,hHost⟩:=hSelect f₀ Nextra
  refine ⟨NHost,hHostGeom,hChainOrder,hExtraOrder,hReserveHost,hBudgetHost,?_⟩
  intro n hn G Dnat hreg hEven F₀ hF₀ Allowed hAllowedNonempty hAllowedValid hFAllowed hLong hmin hαHostLe hδAbs hεQcap htrim
  have hnpos:0<n:=by omega
  have hInputs:=repeated_factor_original_selector_inputs (K:=K) hnpos G F₀ hreg hEven hF₀ Allowed hAllowedNonempty hAllowedValid hFAllowed hLong αRef ρ₀ θ hαRef hρ₀ hρone hmin r
  dsimp only [] at hInputs
  obtain ⟨hDpos,hDlo,hDhi,hU,hAllowed,hclass,hρlo,hρ1,hk₁,hk₂,hNonneg,hSum,hParts,hClass,hρeq⟩:=hInputs
  have hk₁':kstar ≤ initialIndexDensity (Fin (Dnat/2)) Dnat*(1/100)/2:=by rw [hkstar]; exact hk₁
  have hk₂':kstar ≤ initialIndexDensity (Fin (Dnat/2)) Dnat*((1/100)/(((r+4):ℕ):ℝ))/2:=by rw [hkstar]; exact hk₂
  exact hHost n hn (Fin (Dnat/2)) (fun _=>F₀) (fun _=>hF₀) Allowed hAllowed hAllowedNonempty hAllowedValid hclass G Dnat hreg hmin hρlo hρ1 hEven hαHostLe hδAbs hεQcap htrim hk₁' hk₂' Unit (fun _=>1) () hNonneg hSum (fun _=>Or.inr hrPartOne) hrPartOne hρeq
end Oberwolfach
