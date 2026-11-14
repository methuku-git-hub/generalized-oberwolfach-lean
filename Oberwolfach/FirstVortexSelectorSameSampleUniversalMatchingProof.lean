module

public import Oberwolfach.FirstVortexSelectorSameSampleUniversalMatchingDef

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

theorem first_vortex_selector_with_same_sample_universal_matching
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
    (ρreserve κaux ζlocal s c:ℝ)
    (βListInit εLevelInit hostCapInit:ℝ)
    (hInitial:FirstVortexInitialMatchingVortexRates ρ₀ δglobal βListInit βfinal εLevelInit εInner εAbs εRob γRich kstar tstar hostCapInit bmatch α εQ)
    (hRet:FirstVortexRetentionBalanceRates r d εQ active θ s c ζret ζlocal ηBalance κaux)
    (hcutHost:5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (hlamhi:lam≤α/128) (hρreserve:0≤ρreserve)
    (hListMargin:βfinal+2*ρreserve≤((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/2)
    (hγRich:0≤γRich) (hζStable:0≤ζStable)
    (hSel:FirstVortexSelectorWithUniversalParentChain r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall αHost rPart ζret hαHost hrPart hζret hεQHost
      K hK3 hm θ hθpos hθ htstarBound d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap α δold δlocal bmatch cLocal):
    FirstVortexSelectorWithSameSampleUniversalMatching r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
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
  intro γLevel σLevel κmax κauxCap ζCap hγLevel hσLevel hκmax hκaux hζCap
  obtain ⟨gammaLoss,sigmaLoss,hGamma,hSigma,hGammaCap,hSigmaCap,hGammaOrd,
    ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap',hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,
    χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,hh⟩:=
    hh γLevel σLevel κmax κauxCap ζCap hγLevel hσLevel hκmax hκaux hζCap
  refine ⟨gammaLoss,sigmaLoss,hGamma,hSigma,hGammaCap,hSigmaCap,hGammaOrd,
    ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap',hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,
    χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,?_⟩
  intro ζ εBal ζBal hζ hεBal hζBal Qreal pstarRef ζNbr εLoad ζLoad ζLocal ζConfig τLevel hNbr
  have hh:=hh ζ εBal ζBal hζ hεBal hζBal
  intro δparent hδparent
  obtain ⟨βmax,hβmax,hGeom⟩:=hh δparent hδparent
  refine ⟨βmax,hβmax,?_⟩
  intro κgeom hcutGeom ξGeom xiDeep ωGeom xGeom NGeom NIGeom hNGeom hαRef he8 heAlpha hκgeom heκ hecut heξ hedeep hωGeom hωv hωu hxGeom A hHostGeom
  obtain ⟨βQ,hβQ,hβquarter,hβα4,hβmax',hβbal,hβref,MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀cap,hΔ,hξ,hξrate,
    mGeom,hmGeom,vsize,hvsize,hmLevelSize,hmGeomSize,τHost,hτHost,hτHostBound,NHostGeom,hNHostGeom,hHostLate,
    ξResidual,hξResidual,hξResidualBound,hζOrdResidual,hξResidualBound2,hξSeedResidual,hResidualScales,
    ζList,hζList,hζListCap,N,a₀,b₀,e₀,aRob,bRob,eRob,aParent,bParent,eParent,aStable,bStable,eStable,Nchain,hChain,hSelect⟩:=
      hGeom κgeom hcutGeom ξGeom xiDeep ωGeom xGeom NGeom NIGeom hNGeom hαRef he8 heAlpha hκgeom heκ hecut heξ hedeep hωGeom hωv hωu hxGeom A hHostGeom
  have hMatching:=first_vortex_parent_and_universal_matching_at α lam lamAssign εQ δold δlocal δglobal θ epsOrd ξResidual ρ₀ bmatch ξClassOrd ζret d K r ζOrd rho δLoss εInner eta eRob
    cap cLocal active ηBalance κPack βfinal Nchain hChain
  refine ⟨βQ,hβQ,hβquarter,hβα4,hβmax',hβbal,hβref,MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀cap,hΔ,hξ,hξrate,
    mGeom,hmGeom,vsize,hvsize,hmLevelSize,hmGeomSize,τHost,hτHost,hτHostBound,NHostGeom,hNHostGeom,hHostLate,
    ξResidual,hξResidual,hξResidualBound,hζOrdResidual,hξResidualBound2,hξSeedResidual,hResidualScales,
    ζList,hζList,hζListCap,N,a₀,b₀,e₀,aRob,bRob,eRob,aParent,bParent,eParent,aStable,bStable,eStable,Nchain,hChain,?_⟩
  intro f₀ Nextra
  obtain ⟨NHost,hHostGeom,hChainOrder,hExtraOrder,hHost⟩:=hSelect f₀ Nextra
  refine ⟨NHost,hHostGeom,hChainOrder,hExtraOrder,?_⟩
  intro n hn U _ _ F hF Allowed hAllowed hAllowedNonempty hAllowedValid hclass G Dnat hreg hmin hρlo hρ1 hEven hαHostLe hδAbs hεQcap htrim hk₁ hk₂ Itype _ density iclass hdensity hsum hparts hiclass hρeq
  have hnChain:Nchain≤n:=by omega
  letI : Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
  obtain ⟨Q,π,hpres,w,weight,hD,hsize,hnoshort,hU,hDnat,hDlo,hDhi,hmargin,hv,hGeo,hw0,hwupper,hedges,hbudgetV,hbudgetE,hwK,hRest⟩:=
    hHost n hn U F hF Allowed hAllowed hAllowedNonempty hAllowedValid hclass G Dnat hreg hmin hρlo hρ1 hEven hαHostLe hδAbs hεQcap htrim hk₁ hk₂ Itype density iclass hdensity hsum hparts hiclass hρeq
  refine ⟨Q,π,hpres,w,weight,hD,hsize,hnoshort,hU,hDnat,hDlo,hDhi,hmargin,hv,hGeo,hw0,hwupper,hedges,hbudgetV,hbudgetE,hwK,?_⟩
  obtain ⟨weightParent,weightActive,hParentWeight,hActiveWeight,levelWeight,hLevelWeight,z,hMass,hPrior,hParent,hExpanded,hStable,hProtected,hEvery,hBoundary,hBound⟩:=hRest
  refine ⟨weightParent,weightActive,hParentWeight,hActiveWeight,levelWeight,hLevelWeight,z,hMass,hPrior,hParent,hExpanded,hStable,hProtected,hEvery,hBoundary,hBound,?_⟩
  intro hReserve hκcap hζcap
  have hL:Q.length-1+1=Q.length:=by have hh:=Q.length_pos;omega
  have hUpos:0<Fintype.card U:=(first_vortex_density_identity n Dnat ρ₀ hDnat hρ₀ hρlo hρ1 hDhi).2.2.1
  have hρpos:0< initialIndexDensity U Dnat:=lt_of_lt_of_le hρ₀ hρlo
  have hεα:εQ≤α/1000:=by rcases hInitial with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hh,_⟩;exact hh
  have hεδ:εQ≤δglobal:=by rcases hInitial with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hh,_⟩;exact hh
  have hζretRate:ζret≤θ/4096:=hRet.2.2.2.2.2.2.1
  have hηBalance:0<ηBalance:=hRet.2.2.1
  have hκauxPos:0<κaux:=hRet.2.2.2.1
  have hκauxRet:κaux≤ζret:=hRet.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hκauxRate:κaux≤ηBalance/(8*((((r+4):ℕ):ℝ)+1)):=hRet.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcutMatch:(1/((r:ℝ)+4+1))/(d:ℝ)≤θ:=by simpa only [Nat.cast_add,Nat.cast_ofNat] using hcut
  have hdec6:referenceWitnessFinDecidable 6=instDecidableEqFin 6:=Subsingleton.elim _ _
  have hNumMatch:=hMatching n hnChain U G π Dnat vsize βQ Q hreg hDnat hρ1 hρlo hDlo hDhi hvsize F hF Allowed hAllowed hclass hcutMatch hcutHost hnoshort
    hεα hlamhi (min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))) (min (epsOrd/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))) (θ/4096) ξSeed ΔSeed rfl rfl rfl hζOrdE hξSeedResidual hζOrdSeed hepsOrd1 hζretRate hζret.le
    τHost A BM hBM weight hwK BO hBO w hw0 hwupper z (fun _=>True) trivial ζ hζcap (Q.extendedVertices 1)
    ((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) tSeed τHost hτHost.le hBoundary
    gammaLoss sigmaLoss (2*vsize) aRob bRob eRob f₀ (Q.length-1) eRob εRob ζCorr ξCorr (by omega) hL hpres hξCorr.le (hbudget n) hεQRob (le_refl _) hEvery hProtected
    (2*α) ρreserve (by ring) hReserve (le_refl _) hUpos hεδ hU hρreserve hListMargin hζOrdResidual
    1 (by omega) (2*vsize) a₀ b₀ e₀ aRob bRob eRob f₀ (initialIndexDensity U Dnat) hρpos hsize
    β βCommon εAbs εRob ζRob εRef κmax γRich tstar ζ εBal ζBal εNbr 1 (successorWeightUpper k₀ ((2*αRef)/4)) 1 1 1 1 ρ₀ sstar kstar 1 hγRich levelWeight hPrior
    κaux κ hηBalance hκauxPos hκ.le (hκaux'.trans hκcap) hεRefEq hεNbr.le (hεNbrCap.trans hκcap) hκauxRate hκauxRet
    εStable ζStable capStable (2*vsize) aStable bStable eStable f₀ hζStable hStable
  have hAlpha:(2*α)/2=α:=by ring
  simpa only [hAlpha] using hNumMatch.2
end Oberwolfach
