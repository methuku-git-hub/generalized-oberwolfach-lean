module

public import Oberwolfach.FirstVortexNamedTailAtMatchingActualHostHighProbabilityNoCompletionDef

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

theorem first_vortex_named_tail_at_matching_actual_host_high_probability_no_completion
    (r h k₀ Qpow:ℕ) (αRef sstar ω γRich tstar kstar ρ₀:ℝ) (hρ₀:0<ρ₀)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (εQ:ℝ) (hεQ:0<εQ) (hεQ1:εQ<1/4) (hεQAbs:εQ≤εAbs) (hεQRob:εQ≤εRob)
      (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ:ℝ) (hθpos:0<θ) (hθ:θ≤1/100)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (d:ℕ) (hd:2≤d) (cBoundary:ℝ) (hcBoundary:0<cBoundary) (hspacing:4/(d:ℝ)≤cBoundary) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (lam:ℝ) (hlam:0<lam) (hlamθ:lam≤θ) (ξCap:ℝ) (hξCap:0<ξCap)
    (α cLocal chainCap active lamAssign δglobal δold δlocal bmatch ζret ηBalance κPack βfinal cap rho eta δLoss εInner:ℝ) (hζret:0<ζret)
    (gammaStep sigmaStep κaux κmax δparent εBal ζBal:ℝ)
    (κgeom hcutGeom ξGeom xiDeep ωGeom xGeom:ℝ) (NGeom NIGeom:ℕ) (A:ℝ)    (hTail:FirstVortexNamedTailAtMatchingGeometrySizedHighProbabilityNoCompletion r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall K hK3 hm θ hθpos hθ htstarBound
      d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap
      α cLocal chainCap active lamAssign δglobal δold δlocal bmatch ζret ηBalance κPack βfinal cap rho eta δLoss εInner hζret gammaStep sigmaStep κaux κmax δparent εBal ζBal κgeom hcutGeom ξGeom xiDeep ωGeom xGeom NGeom NIGeom A):
    FirstVortexNamedTailAtMatchingActualHostHighProbabilityNoCompletion r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall K hK3 hm θ hθpos hθ htstarBound
      d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap
      α cLocal chainCap active lamAssign δglobal δold δlocal bmatch ζret ηBalance κPack βfinal cap rho eta δLoss εInner hζret gammaStep sigmaStep κaux κmax δparent εBal ζBal κgeom hcutGeom ξGeom xiDeep ωGeom xGeom NGeom NIGeom A :=by
  obtain ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,hNumeric,hRest⟩:=hTail
  refine ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,hNumeric,?_⟩
  obtain ⟨eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,hRest⟩:=hRest
  refine ⟨eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,?_⟩
  intro χTarget hχTarget
  obtain ⟨ε₀,ηEvent,hε₀,hε₀one,hηEvent,hprob,hχBudget,hRest⟩:=hRest χTarget hχTarget
  refine ⟨ε₀,ηEvent,hε₀,hε₀one,hηEvent,hprob,hχBudget,?_⟩
  intro rPart hrPart
  have hPreparedBulkChunks1 :=hRest rPart hrPart
  obtain ⟨εExtra,hExtra,hExtraBound,gammaLoss,sigmaLoss,extra,hγLoss,hσLoss,hextra,hγOrd,hγBudget,hσBudget,hPreparedBulkChunks1Rest1⟩:=hPreparedBulkChunks1
  obtain ⟨ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap,hξCorr,hξCorrRate,hbudget,hPreparedBulkChunks1Rest2⟩:=hPreparedBulkChunks1Rest1
  obtain ⟨hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,χ,χCommon,χBal,hPreparedBulkChunks1Rest3⟩:=hPreparedBulkChunks1Rest2
  obtain ⟨χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,hPreparedBulkChunks1Rest4⟩:=hPreparedBulkChunks1Rest3
  obtain ⟨βmax,hβmax,βQ,hβQ,hβquarter,hβα4,hβmax',hβbal,hβref,mGeom,hmGeom,MLevel,hPreparedBulkChunks1Rest5⟩:=hPreparedBulkChunks1Rest4
  obtain ⟨hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀cap,hPreparedBulkChunks1Rest6⟩:=hPreparedBulkChunks1Rest5
  obtain ⟨hΔ,hξ,hξrate,vsize,hvsize,hmLevelSize,hmGeomSize,τHost,hτHost,hτHostBound,NHostGeom,hNHostGeom,hPreparedBulkChunks1Rest7⟩:=hPreparedBulkChunks1Rest6
  obtain ⟨hHost,ξResidual,hξResidual,hξResidualBound,hζOrdResidual,hξResidualBound2,hξSeedResidual,hResidualScales,ζList,hζList,hζListCap,N,hPreparedBulkChunks1Rest8⟩:=hPreparedBulkChunks1Rest7
  obtain ⟨a₀,b₀,e₀,aRob,bRob,eRob,aParent,bParent,eParent,aStable,bStable,eStable,hPreparedBulkChunks1Rest9⟩:=hPreparedBulkChunks1Rest8
  obtain ⟨Nchain,hChain,Nprep,hPrep,hRest⟩:=hPreparedBulkChunks1Rest9
  refine ⟨εExtra,hExtra,hExtraBound,gammaLoss,sigmaLoss,extra,hγLoss,hσLoss,hextra,hγOrd,hγBudget,hσBudget,
    ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap,hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,
    χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,
    βmax,hβmax,βQ,hβQ,hβquarter,hβα4,hβmax',hβbal,hβref,mGeom,hmGeom,MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀cap,hΔ,hξ,hξrate,
    vsize,hvsize,hmLevelSize,hmGeomSize,τHost,hτHost,hτHostBound,NHostGeom,hNHostGeom,hHost,
    ξResidual,hξResidual,hξResidualBound,hζOrdResidual,hξResidualBound2,hξSeedResidual,hResidualScales,
    ζList,hζList,hζListCap,N,a₀,b₀,e₀,aRob,bRob,eRob,aParent,bParent,eParent,aStable,bStable,eStable,Nchain,hChain,Nprep,hPrep,?_⟩
  intro f₀
  obtain ⟨NHost,hGeomHost,hChainHost,hPrepHost,hExtraHost,hFor⟩:=hRest f₀
  refine ⟨NHost,hGeomHost,hChainHost,hPrepHost,hExtraHost,?_⟩
  intro n hn U _ _ F hF Allowed hAllowed hAllowedNonempty hAllowedValid hclass G Dnat hreg hmin hρlo hρ1 hEven hδAbs hεQcap htrim hk₁ hk₂
  have hnGeom:NHostGeom≤n:=by omega
  obtain ⟨Q,π,hpres,hnoshort,hU,hDnat,hDreal,hDlo,hDhi,hmargin,hsize,hdeg,hv,hLen,hGeo,w,weight,hw0,hwupper,hedges,hbudgetV,hbudgetE,hwK⟩:=
    hHost Allowed hAllowedNonempty hAllowedValid n hnGeom U F hF hAllowed θ hθpos hθ hcut hclass G Dnat hreg hmin hρlo hρ1
  have hL:Q.length-1<Q.length:=by have hh:=Q.length_pos;omega
  have hvsize:vsize≤n:=by omega
  have hSelected:=hFor n hn U F hF Allowed hAllowed (initialIndexDensity U Dnat) (Dnat:ℝ)
    hρlo hρ1 hDreal hsize hclass G π τHost A weight hwK hDlo hDhi w hw0 hwupper hU hnoshort
    0 hedges hdeg hbudgetV hbudgetE hτHost.le hτHostBound hδAbs Dnat vsize rfl rfl hreg hmargin hmLevelSize hvsize
    Q (by omega) hεQcap htrim hpres (Q.length-1) hL hk₁ hk₂ htstarBound hEven hmargin
  exact ⟨Q,π,hpres,w,weight,hDreal,hsize,hnoshort,hU,hDnat,hDlo,hDhi,hmargin,hv,hGeo,hw0,hwupper,hedges,hbudgetV,hbudgetE,hwK,hSelected⟩
end Oberwolfach
