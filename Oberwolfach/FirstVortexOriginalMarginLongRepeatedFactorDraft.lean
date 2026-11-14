module

public import Oberwolfach.FirstVortexOriginalMarginSelectorUniversalMatchedGeometryFactorSeed
public import Oberwolfach.FirstVortexSelectorGeometryBudgetFactorSeed
public import Oberwolfach.FirstVortexRepeatedSelectorAtGeometryBudgetProof
public import Oberwolfach.FirstVortexRepeatedSelectorFactorDecompositionCaller

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

theorem first_vortex_original_margin_long_repeated_factor (α:ℝ) (hα:0<α) :
    ∃K N:ℕ,∀n≥N,∀(G:SimpleGraph (Fin n)) (D:ℕ),G.IsRegularOfDegree D→Even D→
      ∀F₀:SimpleGraph (Fin n),F₀.IsRegularOfDegree 2→∀Allowed:Set ℕ,
      Allowed.Nonempty→(∀s∈Allowed,3≤s)→AllowedCycleLengths F₀ Allowed→factorPreparationClass F₀ K=none→
      (allowedThreshold Allowed+α/2)*n≤(D:ℝ)→
      HasFactorDecomposition G (fun _:Fin (D/2)=>F₀) :=by
  obtain ⟨αRef,κL,ρ₀,href,hρ,hrefCap,hrefAlpha,hκL,hκLcap,hρone,hρκ,hmargin,hOuter⟩:=
    first_vortex_original_margin_selector_universal_matched_geometry_factor_seed α hα
  obtain ⟨m,r,k₀,hm,hL,heven,hr,hrm,hlen,hcycle,htrim,A,BM,hA,hBM,hHostCont,hm',htstar,hTail⟩:=hOuter 0
  obtain ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,
    εStable,ζStable,capStable,hεStable,hζStable,hcapStable,hSelector,hBA,
    βfinal,ρreserve,hβfinal,hβone,hβlist,hρreserve,hreserveList,hreserveSize,
    zetaCfg,betaA,hzeta,hbetaA,hbetaCfg,hbetaCommon,hcycleFixed,hpathFixed,
    Kgeom,hKgeom,kappa0,ξ,thetaDeep,kappa,hkappa0,hξ,hthetaDeep,hkappa,hkappaLe,
    ζCut,hIcut,εLevel,deltaI,hζcut,hζcut1,hζcutT,hIcut0,hIcutA,hIcutT,
    hεLevel,hεCut,hεξ,hεκ,hεα,hεone,hδI,hδIone,hδIα,hδIk,hδIt,
    cap,hcap,hcapStable',hChosen,
    rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hGlobal,
    bmatch,αMatch,ε,hInitial,hεStable',hεHost,hLevel,hSelectorNumeric⟩:=hTail
  obtain ⟨hbmatch,hbmatchCap,hαMatch,hmatch,hmglobal,hε,hε1,hεLevel',hεInner',hεAbs',hεRob',hεcap,hεsmall,hεMatch,hεαMatch,hερ,hερ2,hεδ,hβsum⟩:=hInitial
  have heLevel:ε≤εLevel:=hεLevel'.trans (min_le_left _ _)
  have he8:ε≤1/8:=heLevel.trans hεone
  have heAlpha:ε≤αRef/8:=heLevel.trans hεα
  have heκ:ε≤kappa:=heLevel.trans hεκ
  have hecut:ε≤hIcut:=heLevel.trans hεCut
  have heξ:4*ε≤ξ:=by nlinarith
  obtain ⟨omegaInner,xiDeep,hω,hωone,hxi,hωε,hωρ,hεxi,hxiξ,hxiκ,hDeepSource,
    betaExt,epsilonExt,betaRec,zetaCommon,hbe,hee,hbr,hzc,hzck,hbre,hbra,hbrt,hbrc,hbrp,gammaMax,hgm,
    gammaStep,hgs,hgmax,hgcap,etaLevel,ηEnd,ζ,ζD,pmax,heta,hηEnd,hζ0,hζD,hpmax,hpmax8,θLevel,hθLevel,delta,hδ,hx,hxδ,
    sigmaMax,hsmax,sigmaStep,gammaLoss,sigmaLoss,extra,ζCorr,hs,hsle,hg,hgle,hsl,hextra,hgeq,hseq,hcorr,hcorrRob,hbudget,hhost,
    etaBal,hηBal,δSelected,εSelected,ζSelected,hδsel,hεsel,hζsel,NI,NGeom,hNGeom,hReady,
    tolRef,ζActive,τParent,tolParent,ζParent,τ,tolLocal,ζLocal,rowErr,ζRow,epsBal,ζBal,
    htolRef,htolRef1,hζActive,hζActive1,hRefκ,hRefx,hActiveκ,
    hτParent,hτParent1,htolParent,htolParent1,hζParent,hζParent1,hParentκ,hParentDeep,
    hτ,hτ1,htolLocal,htolLocal1,hτlocal,hζLocal,hζLocal1,hLocal,
    hrowErr,hrowErr1,hζRow,hζRow1,hRow,hεBal,hεBal1,hζBal,hζBal1,hBal,hMargin,hWide,
    ζWide,δparent,hζWide,hζWide1,hδparent,hδcfg,hδcommon,hδcut,hδκ,hcycle,hpath,hδref,hδendpoint,hδparentκ,hδparentDeep,hδlocal,hδwide,hδrow,hδcutBound,hParent,hActual,hActualSelected,hAt,hSteps⟩:=hLevel
  obtain ⟨δold,δlocal,hold,hold1,hgap,hδlocalGlobal,hchosen,hchosenCap,hc,hactive,hactiveLocal,hactiveTransfer,hactiveGlobal,
    hθcap,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκcap,hlamcap,hCaller⟩:=hReady
  obtain ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htCap,hs0,hAssign,hAssignCap,hθ,hθs,hθCap,
    hκPack,hκs,hκCap',hθκ,hceiling,hlam,hξCap,hlams,hlamCap',hξs,hξCap',hlamθ,hlamα,hlamδ,hCap,hD⟩:=hCaller
  obtain ⟨d,hdExtra,hd3,hdlarge,hspacing,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hRet,Ncaller,hK⟩:=hD 0
  obtain ⟨K,hKExtra,hK3,hcutHost,hNumeric,hNumFor,hK3',hθ',hθ100',hd2,hζret,hlam',hlamθ',hξCap'',hcut',hSelect⟩:=hK 0
  obtain ⟨BO,hBO,hHost⟩:=hHostCont K d (by omega) hd2
  have hcBoundary:0<(4:ℝ)/(d:ℝ):=by positivity
  have hHost':HostMatchingVortexContinuation (r+4) K d (2*αRef) A BM BO:=by simpa [hrm] using hHost
  have hSelected:=hSelect 1 (by norm_num) (4/(d:ℝ)) hcBoundary (le_refl _) BM hBM BO hBO
  let localCap:=markedExplicitJointLocalCap (r+4) (r+12) etaBal (delta/2)
  let transferCap:=Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r (2*αRef)
    (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) zetaCfg etaLevel
    (successorWeightUpper k₀ ((2*αRef)/4)) (ρ₀/(800*((r+4:ℕ):ℝ))) hzeta heta
    (successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2.le (by positivity) (by positivity))
  let cLocal:=min localCap (4*transferCap)
  let c:=min cLocal (min cap (1:ℝ))
  let active:=c/4
  have hBudget:=first_vortex_selector_geometry_budget_factor_seed r (r+12) k₀ 1 αRef (1/100) (ρ₀/4) (min αRef (1/2:ℝ)/2)
    (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) ρ₀ hρ
    β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
    cap rho eta δLoss εInner δglobal cLocal active lamAssign ηBalance κPack βfinal
    ε hε hε1 hεAbs' hεRob' hεsmall (2*αRef) 1 ζret (by positivity) (by norm_num) hζret hεHost
    K hK3' hm' θ hθ' hθ100' htstar d hd2 (4/(d:ℝ)) hcBoundary (le_refl _) hcut' BM hBM BO hBO
    lam hlam' hlamθ' ξCap hξCap'' αMatch δold δlocal bmatch localCap ρreserve κaux εSelected ζSelected δSelected
    gammaStep sigmaStep (kappa/2) hgs hs kappa hIcut ξ xiDeep omegaInner (delta/2) (NGeom d) NI
    (hNGeom d (by omega)) href he8 heAlpha hkappa heκ hecut heξ hεxi hω.le hωε hωρ hx hSelected
  have hRepeated:=first_vortex_repeated_selector_at_geometry_budget r (r+12) k₀ 1 αRef (1/100) (ρ₀/4) (min αRef (1/2:ℝ)/2)
    (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) ρ₀ hρ
    β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
    cap rho eta δLoss εInner δglobal cLocal active lamAssign ηBalance κPack βfinal
    ε hε hε1 hεAbs' hεRob' hεsmall (2*αRef) 1 ζret (by positivity) (by norm_num) (by norm_num) hζret hεHost
    K hK3' hm' θ hθ' hθ100' htstar d hd2 (4/(d:ℝ)) hcBoundary (le_refl _) hcut' BM hBM BO hBO
    lam hlam' hlamθ' ξCap hξCap'' αMatch δold δlocal bmatch localCap ρreserve κaux εSelected ζSelected δSelected
    gammaStep sigmaStep (kappa/2) hgs hs kappa hIcut ξ xiDeep omegaInner (delta/2) (NGeom d) NI
    (hNGeom d (by omega)) href hρone rfl he8 heAlpha hkappa heκ hecut heξ hεxi hω.le hωε hωρ hx hBudget
  have hLong:=first_vortex_repeated_selector_factor_decomposition_caller r k₀ K d NI Kgeom (NGeom d) αRef ρ₀ href hρ hρone
    β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable hδAbs.le
    cap rho eta δLoss εInner δglobal cLocal active lamAssign ηBalance κPack βfinal
    ε hε hε1 hεAbs' hεRob' hεsmall hεHost hεStable' ζret hζret hK3' hm' θ hθ' hθ100' htstar
    hd2 (4/(d:ℝ)) hcBoundary (le_refl _) hcut' BM hBM BO hBO lam hlam' hlamθ' ξCap hξCap''
    αMatch δold δlocal bmatch ρreserve κaux εSelected ζSelected δSelected gammaStep sigmaStep hgs hs
    kappa hIcut ξ xiDeep omegaInner (delta/2) thetaDeep etaBal etaLevel deltaI (hNGeom d (by omega))
    hkappa hx hthetaDeep heta hηBal hxi.le hxiκ hDeepSource δparent zetaCfg ζCut epsBal ζBal betaA betaRec hzeta
    hAt hbetaCommon hbra hIcut0.le hδIα hδIk hδIt hIcutA hδcut hIcutT hcycleFixed hpathFixed hbrt
    hactiveTransfer s c ζlocal hRet hactive hcap hcapStable' hactiveGlobal hactiveLocal hChosen
    gammaLoss sigmaLoss extra hgeq hseq (hSteps d (by omega)) hεcap htrim A hHost' hRepeated
  obtain ⟨N,hN⟩:=hLong
  refine ⟨K,N,?_⟩
  intro n hn G D hreg hEven F₀ hF₀ Allowed hAllowedNonempty hAllowedValid hFAllowed hLongClass hmin
  exact hN n hn G D hreg hEven F₀ hF₀ Allowed hAllowedNonempty hAllowedValid hFAllowed hLongClass
    (hmargin (allowedThreshold Allowed) D n hmin)
end Oberwolfach
