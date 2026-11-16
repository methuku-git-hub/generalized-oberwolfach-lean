module

public import Oberwolfach.LongProtectedPreparationStatement
public import Oberwolfach.LongOriginalMarginAndEditBudget
public import Oberwolfach.FirstVortexOriginalMatchedNoCompletionBothParentCaps
public import Oberwolfach.FirstVortexNamedTailAtMatchingActualHostHighProbabilityNoCompletionProof
public import Oberwolfach.FirstVortexParentAlignedAtWeightMonotonicity
public import Oberwolfach.FirstVortexUniversalCoreFactorSeedFromJointThreshold
public import Oberwolfach.FirstVortexProtectedPreparationFromFixedReserveSeedFin
public import Oberwolfach.LongAssignedPreparationProbabilityTransferBudgetMono
public import Oberwolfach.ProtectedPreparationMonotone
public import Oberwolfach.LongPreparationFinalBounds

@[expose] public section
/-! Original-assumption long preparation using the selected same-sample construction. -/
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

theorem long_protected_preparation_from_original_two_splits : LongProtectedPreparation :=by
  intro θHost α₀ εmax ρstar hθHost hθHostOne hα₀ hεmax hρstar hρstarOne
  obtain ⟨α,hα,hαcap,hEditCap,hHostMargin⟩:=long_original_margin_and_edit_budget α₀ εmax hα₀ hεmax
  obtain ⟨αRef,κL,ρ₀,href,hρ₀,hrefCap,hrefAlpha,hκL,hκLcap,hρ₀one,hρcap,hρk,hMargin,hHosts,hTail⟩:=
    first_vortex_original_matched_no_completion_both_parent_caps α ρstar hα hρstar
  obtain ⟨m,r,k₀,hm,hL,heven,hr,hrm,hlen,hcycle,htrim,A,BM,hA,hBM,hHostCont,hAfter⟩:=hTail 0
  dsimp only [] at hAfter
  have hPreparedBulkChunks1 :=hAfter
  obtain ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,hPreparedBulkChunks1Rest1⟩:=hPreparedBulkChunks1
  obtain ⟨εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,εStable,ζStable,hPreparedBulkChunks1Rest2⟩:=hPreparedBulkChunks1Rest1
  obtain ⟨capStable,hεStable,hζStable,hcapStable,hLower,hUpper,hSelector,hParentLevel,βfinal,ρreserve,hβfinal,hβfinalOne,hPreparedBulkChunks1Rest3⟩:=hPreparedBulkChunks1Rest2
  obtain ⟨hβList,hρreserve,hreserveBudget,hreserveHost,zetaCfg,hzeta,betaA,hbetaA,hbetaConfig,hbetaCommon,hCycleFixed,hPathFixed,hPreparedBulkChunks1Rest4⟩:=hPreparedBulkChunks1Rest3
  obtain ⟨Kgeom,hKgeom,kappa0,ξGeom,thetaDeep,kappa,hkappa0,hξGeom,hthetaDeep,hkappa,hkappaCap,ζCut,hPreparedBulkChunks1Rest5⟩:=hPreparedBulkChunks1Rest4
  obtain ⟨hIcut,εLevel,deltaI,hζCut,hζCutOne,hζCutSmall,hIcutPos,hIcutAlpha,hIcutTime,hεLevel,hεCut,hεξ,hPreparedBulkChunks1Rest6⟩:=hPreparedBulkChunks1Rest5
  obtain ⟨hεκ,hεα,hεone,hδI,hδIone,hδIα,hδIk,hδIt,cap,hcap,hcapStable,hCapBA,hPreparedBulkChunks1Rest7⟩:=hPreparedBulkChunks1Rest6
  obtain ⟨hCapParent,rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hAmbient,hδglobalBound,hPreparedBulkChunks1Rest8⟩:=hPreparedBulkChunks1Rest7
  obtain ⟨bmatch,αMatch,ε,δold,δlocal,hαMatch,hInitial,hεStableBound,hεHost,hδold,hδoldOne,hδoldGlobal,hPreparedBulkChunks1Rest9⟩:=hPreparedBulkChunks1Rest8
  obtain ⟨hδgap,hδlocalEq,hδlocalGlobal,hm',htstarBound,hLevel⟩:=hPreparedBulkChunks1Rest9
  dsimp only [FirstVortexLevelWithLateGeometryHighProbabilityNoCompletion] at hLevel
  have hPreparedBulkChunks2 :=hLevel
  obtain ⟨omegaInner,xiDeep,hOmegaInner,hOmegaOne,hXiDeep,hOmegaEps,hOmegaRho,hEpsDeep,hDeepGeom,hXiScale,hDeepSource,betaExt,hPreparedBulkChunks2Rest1⟩:=hPreparedBulkChunks2
  obtain ⟨epsilonExt,betaRec,zetaCommon,hBetaExt,hEpsilonExt,hBetaRec,hZetaCommon,hZetaCommonCap,hRecExt,hRecA,hRecTime,hRecCycle,hPreparedBulkChunks2Rest2⟩:=hPreparedBulkChunks2Rest1
  obtain ⟨hRecPath,gammaMax,hGammaMax,gammaStep,hGammaStep,hGammaMaxBound,hGammaCapBound,etaLevel,etaEnd,ζLevel,ζD,pmax,hPreparedBulkChunks2Rest3⟩:=hPreparedBulkChunks2Rest2
  obtain ⟨hEtaLevel,hEtaEnd,hζLevel,hζD,hPmax,hPmaxBound,thetaLevel,hThetaLevel,deltaLevel,hDeltaLevel,hX,hXdelta,hPreparedBulkChunks2Rest4⟩:=hPreparedBulkChunks2Rest3
  obtain ⟨sigmaMax,hSigmaMax,sigmaStep,gammaCore,sigmaCore,extraCore,ζCore,hSigmaStep,hSigmaMaxBound,hGammaCore,hGammaCoreBound,hSigmaCore,hPreparedBulkChunks2Rest5⟩:=hPreparedBulkChunks2Rest4
  obtain ⟨hExtraCore,hGammaSplit,hSigmaSplit,hζCore,hζCoreRob,hCoreBudget,hCoreHost,etaBal,hEtaBal,hLaterLoss,capOne,capTwo,hPreparedBulkChunks2Rest6⟩:=hPreparedBulkChunks2Rest5
  obtain ⟨δFixed,εFixed,ζFixedBal,hCapOne,hCapTwo,hδFixedCut,hδFixedCommon,hWitness,hTransfer,NI,tolRef,ζActive,hPreparedBulkChunks2Rest7⟩:=hPreparedBulkChunks2Rest6
  obtain ⟨τParent,tolParent,ζParent,τLevel,tolLocal,ζLocal,rowErr,ζRow,epsBal,ζBal,hTolRef,hTolRefOne,hPreparedBulkChunks2Rest8⟩:=hPreparedBulkChunks2Rest7
  obtain ⟨hζActive,hζActiveOne,hRefK,hRefX,hActiveK,hτParent,hτParentOne,hTolParent,hTolParentOne,hζParent,hζParentOne,hParentK,hPreparedBulkChunks2Rest9⟩:=hPreparedBulkChunks2Rest8
  obtain ⟨hParentTheta,hτLevel,hτLevelOne,hTolLocal,hTolLocalOne,hLocalEta,hζLocal,hζLocalOne,hLocalBound,hRowErr,hRowErrOne,hζRow,hPreparedBulkChunks2Rest10⟩:=hPreparedBulkChunks2Rest9
  obtain ⟨hζRowOne,hRowTime,hEpsBal,hEpsBalOne,hζBal,hζBalOne,hBalEta,hBalX,hWideFor,ζWide,δparent,hζWide,hPreparedBulkChunks2Rest11⟩:=hPreparedBulkChunks2Rest10
  obtain ⟨hζWideOne,hδparent,hδCfg,hδCommon,hδCut,hδK,hδCycle,hδPath,hδRefK,hδRefX,hδParentK,hδParentTheta,hPreparedBulkChunks2Rest12⟩:=hPreparedBulkChunks2Rest11
  obtain ⟨hδLocalEta,hδWideEta,hδRow,hδCutTime,hParentRates,hActualParentRates,hSteps⟩:=hPreparedBulkChunks2Rest12
  dsimp only [FirstVortexExplicitPreparedTransferWithLateGeometryHighProbabilityNoCompletion] at hTransfer
  obtain ⟨hchosen,hchosenLocal,hc,hactive,hactiveLocal,hactiveTransfer,hactiveGlobal,
    hθcap,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκcap,hlamcap,hCaller,hExact⟩:=hTransfer
  obtain ⟨hε,hε1,hεAbs,hεRob,hεsmall,hCaller⟩:=hCaller
  dsimp only [FirstVortexCallerPreparedChainWithLateGeometryHighProbabilityNoCompletion] at hCaller
  obtain ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htCap,hs,hAssign,hAssignCap,hθ,hθs,hθUpper,
    hκ,hκs,hκCap,hθκ,hceiling,hlam,hξ,hlams,hlamCap,hξs,hξCap,hlamθ,hlamα,hlamδ,hClassCap,hD⟩:=hCaller
  obtain ⟨d,hdExtra,hd3,hdlarge,hspacing,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hRet,Nchain0,hK⟩:=hD 1
  obtain ⟨K,hKExtra,hK3,hcutHost,hNumeric,hTail,hRest⟩:=hK 0
  have hInitialCopy:=hInitial
  obtain ⟨hbmatch,hbmatchCap,hαMatchPos,hαMatchCap,hαglobal,hεpos',hεquarter',hεLevelBound,hεinner,hεAbs',hεRob',hεList,hεsmall',hεHost',hεMatch,hεRho,hεrate,hεδglobal,hListBudget⟩:=hInitialCopy
  have hεLevel' : ε≤εLevel := hεLevelBound.trans (min_le_left _ _)
  have hWitnessCopy:=hWitness
  dsimp only [FirstVortexActualParentAlignedWitness] at hWitnessCopy
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hεFixedPos,_⟩:=hWitnessCopy
  obtain ⟨Ngeom,hNgeom,hStepsAt⟩:=hSteps d (by omega)
  obtain ⟨BO,hBO,hHostCont'⟩:=hHostCont K d (by omega) (by omega)
  have hHostGeom : HostMatchingVortexContinuation (r+4) K d (2*αRef) A BM BO := by simpa only [hrm] using hHostCont'
  obtain ⟨hθpos,hθone,hK3',hd2,hboundary,hspace,hcut',hlam',hlamθ',hξ',hζret,hFor⟩:=hTail
  have hGeomTail:=hFor BM hBM BO hBO kappa hIcut ξGeom xiDeep omegaInner (deltaLevel/2) Ngeom NI A
    hNgeom href (hεLevel'.trans hεone) (hεLevel'.trans hεα) hkappa (hεLevel'.trans hεκ) (hεLevel'.trans hεCut)
    (by nlinarith only [hεLevel',hεξ]) hEpsDeep
    hOmegaInner.le hOmegaEps hOmegaRho hX hεFixedPos hHostGeom
  have hActualTail := first_vortex_named_tail_at_matching_actual_host_high_probability_no_completion
    r (r+12) k₀ 1 αRef (1/100) (ρ₀/4) (min αRef (1/2:ℝ)/2) (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) ρ₀ hρ₀
    β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
    ε hε hε1 hεAbs hεRob hεsmall K hK3' hm' θ hθpos hθone htstarBound d hd2 _ hboundary hspace hcut'
    BM hBM BO hBO lam hlam' hlamθ' ξCap hξ'
    αMatch _ _ _ lamAssign δglobal δold δlocal bmatch ζret ηBalance κPack βfinal cap rho eta δLoss εInner hζret
    gammaStep sigmaStep κaux (kappa/2) δFixed εFixed ζFixedBal kappa hIcut ξGeom xiDeep omegaInner (deltaLevel/2) Ngeom NI A hGeomTail
  have hBAParent : 0≤successorWeightUpper k₀ ((2*αRef)/4) :=
    (successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2.le
  have hAtBig := first_vortex_parent_aligned_witness_to_at r ρ₀ (1/100) (1/(200*((r+4:ℕ):ℝ)))
    (successorWeightUpper k₀ (αRef/4)) δFixed zetaCfg kappa (deltaLevel/2) thetaDeep etaLevel ε etaBal capOne capTwo betaA
    (markedLocalCycleCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ))))
    (markedLocalPathCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ))))
    δFixed εFixed ζFixedBal (le_refl δFixed) hWitness
  have hAtSmall := first_vortex_parent_aligned_at_weight_monotonicity r ρ₀ (1/100) (1/(200*((r+4:ℕ):ℝ)))
    (successorWeightUpper k₀ ((2*αRef)/4)) (successorWeightUpper k₀ (αRef/4)) δFixed zetaCfg kappa (deltaLevel/2) thetaDeep etaLevel ε etaBal capOne capTwo betaA
    (markedLocalCycleCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ))))
    (markedLocalPathCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ))))
    δFixed εFixed ζFixedBal hρ₀ (by norm_num) hε hBAParent hUpper hAtBig
  obtain ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,hNumeric,hRest⟩:=hActualTail
  obtain ⟨eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,hRest⟩:=hRest
  refine ⟨K,hK3,ξClassOrd,hξClassOrd,?_⟩
  intro χTarget hχTarget hχTargetOne
  obtain ⟨ε₀,ηEvent,hε₀,hε₀one,hηEvent,hprob,hχBudget,hRest⟩:=hRest χTarget hχTarget
  have hPreparedBulkChunks3 :=hRest 1 (by norm_num)
  obtain ⟨εExtra,hExtra,hExtraBound,gammaLoss,sigmaLoss,extra,hγLoss,hσLoss,hextra,hγLossOrd,hγBudget,hσBudget,hPreparedBulkChunks3Rest1⟩:=hPreparedBulkChunks3
  obtain ⟨ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap,hξCorr,hξCorrRate,hbudget,hPreparedBulkChunks3Rest2⟩:=hPreparedBulkChunks3Rest1
  obtain ⟨hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,χ,χCommon,χBal,hPreparedBulkChunks3Rest3⟩:=hPreparedBulkChunks3Rest2
  obtain ⟨χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,hPreparedBulkChunks3Rest4⟩:=hPreparedBulkChunks3Rest3
  obtain ⟨βmax,hβmax,βQ,hβQ,hβquarter,hβα4,hβmax',hβbal,hβref,mGeom,hmGeom,MLevel,hPreparedBulkChunks3Rest5⟩:=hPreparedBulkChunks3Rest4
  obtain ⟨hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀cap,hPreparedBulkChunks3Rest6⟩:=hPreparedBulkChunks3Rest5
  obtain ⟨hΔ,hξ,hξrate,vsizeHost,hvsizeHost,hmLevelSize,hmGeomSize,τHost,hτHost,hτHostBound,NHostGeom,hNHostGeom,hPreparedBulkChunks3Rest7⟩:=hPreparedBulkChunks3Rest6
  obtain ⟨hHost,ξResidual,hξResidual,hξResidualBound,hζOrdResidual,hξResidualBound2,hξSeedResidual,hResidualScales,ζList,hζList,hζListCap,N,hPreparedBulkChunks3Rest8⟩:=hPreparedBulkChunks3Rest7
  obtain ⟨a₀,b₀,e₀,aRob,bRob,eRob,aParent,bParent,eParent,aStable,bStable,eStable,hPreparedBulkChunks3Rest9⟩:=hPreparedBulkChunks3Rest8
  obtain ⟨Nchain,hChain,Nprep,hPrep,hRest⟩:=hPreparedBulkChunks3Rest9
  obtain ⟨NHost,hGeomHost,hChainHost,hPrepHost,hExtraHost,hHostFor⟩:=hRest 0
  obtain ⟨Nreserve,hReserveScale⟩:=hreserveHost eRob
  let Nbudget:=Classical.choose (marked_vortex_terminal_budget eStable gammaStep sigmaStep hGammaStep hSigmaStep)
  let Bfinal:=max eRob 1
  let Nfinal:=max 1 (max N (max NHost (max Nreserve Nbudget)))
  refine ⟨Bfinal,Nfinal,le_max_right _ _,le_max_left _ _,?_⟩
  intro n hn P D q hreg hEven hmind ρOriginal hρloOriginal hρhiOriginal F hF hcycleOriginal hlong
  have hN1:1≤n := (le_max_left 1 _).trans hn
  have hNcut:N≤n := (le_max_left N _).trans ((le_max_right 1 _).trans hn)
  have hNHost:NHost≤n := (le_max_left NHost _).trans ((le_max_right N _).trans ((le_max_right 1 _).trans hn))
  have hNreserve:Nreserve≤n := (le_max_left Nreserve _).trans ((le_max_right NHost _).trans ((le_max_right N _).trans ((le_max_right 1 _).trans hn)))
  have hNbudget:Nbudget≤n := (le_max_right Nreserve _).trans ((le_max_right NHost _).trans ((le_max_right N _).trans ((le_max_right 1 _).trans hn)))
  have hn0:0<n:=lt_of_lt_of_le (by decide : 0<1) hN1
  letI : Nonempty (Fin n):=⟨⟨0,hn0⟩⟩
  have hmarginOriginal := hHostMargin θHost (D:ℝ) n hmind
  obtain ⟨Allowed,hAllowedNE,hAllowed3,hThreshold,hhostmin,hAllowed,hclass,hq,hD,hDlo,hDhi,hDmargin,hρloHost,hρhiHost,hρsize,hqcard⟩:=
    hHosts n q D K hn0 θHost hmarginOriginal hρloOriginal hρhiOriginal P hreg F hF hcycleOriginal hlong
  obtain ⟨sstar,tstar,kstar,hsstar,htstar,hkstar,hsstarpos,hsstarcap,htstarpos,htstarone,htstars,htstarm,
    hkstarpos,hkstarhalf,hkbudget,hRates⟩:=first_vortex_seed_density_hierarchy r ρ₀ hρ₀ hρ₀one
  obtain ⟨hk₁,hk₂,_,_,_,_,_,_,_,_⟩:=hRates (initialIndexDensity (Fin q) D) tstar hρloHost hρhiHost (le_refl _)
  have hk₁' : ρ₀/(800*((r+4:ℕ):ℝ)) ≤ initialIndexDensity (Fin q) D*(1/100)/2 := by simpa only [hsstar,hkstar] using hk₁
  have hk₂' : ρ₀/(800*((r+4:ℕ):ℝ)) ≤ initialIndexDensity (Fin q) D*((1/100)/(((r+4):ℕ):ℝ))/2 := by
    rw [hsstar,hkstar] at hk₂
    convert hk₂ using 1 <;> ring
  obtain ⟨Q,π,hpres,w,weight,hDreal,hsize,hnoshort,hU,hDnat,hDlo',hDhi',hmargin,hvsize,hGeo,hw0,hwupper,hedges,hbudgetV,hbudgetE,hwK,weightParent,weightActive,hParentW,hActiveW,levelWeight,hLevelW,hProb⟩:=
    hHostFor n (max_le (max_le hNcut hNHost) hN1) (Fin q) F hF Allowed hAllowed hAllowedNE hAllowed3 hclass P D hreg hhostmin hρloHost hρhiHost hEven hδAbs.le hεList htrim hk₁' hk₂'
  let chainCap:=markedExplicitJointLocalCap (r+4) (r+12) etaBal (deltaLevel/2)
  let transferCap:=Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r (2*αRef)
    (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) zetaCfg etaLevel
    (successorWeightUpper k₀ ((2*αRef)/4)) (ρ₀/(800*((r+4:ℕ):ℝ)))
    hzeta hEtaLevel hBAParent (by positivity) (by positivity))
  let c:=min (min chainCap (4*transferCap)) (min cap (1:ℝ))
  let active:=c/4
  let ρHost:=initialIndexDensity (Fin q) D
  let p₁:=ρHost*(1/100)/2
  let k₁:=ρHost*((1/100)/(((r+4):ℕ):ℝ))/2
  let p₂:=(∑u,longAssignedApproxOrdinaryWeight F hF K (r+4) θ u)/(D:ℝ)
  let k₂:=(∑u,longAssignedApproxMarkedWeight F hF K (r+4) θ u)/(D:ℝ)
  let udens:=2*(∑u,(1-1/100-(1/100)/(((r+4):ℕ):ℝ)-longAssignedApproxMarkedWeight F hF K (r+4) θ u-
    longAssignedApproxOrdinaryWeight F hF K (r+4) θ u))/(D:ℝ)
  let qAssigned:=longAssignedIntervalProbability F hF K (r+4) θ
  let sAssigned:=longAssignedSpokeProbability F hF K (r+4) θ
  let hLaw:=long_assigned_actual_raw_law_parameters hn0 F hF Allowed hAllowed K (lt_of_lt_of_le (by decide : 0<3) hK3) (r+4) d hm' hd2 θ ρ₀ ρHost (D:ℝ)
    hθpos.le hθone hρ₀ hρloHost hρhiHost hDreal hsize hcut' hclass
  let μraw:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ udens
    hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1
    d hd2 qAssigned hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 sAssigned
    hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2)
  let f:=fun (ω:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e) e=>
    rawExpandedMarkedCollapse e (ω e)
  let ν:=fun raw:RawMarkedOutcome (Fin n) (Fin q) Bool Bool=>
    startRetentionLaw (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
  let μ:=μraw.sigma (fun ω=>ν (f ω))
  let ParentGood:=fun z:MarkedExpandedActualOutcome (U:=Fin q) π d=>
    MarkedVortexParentRecordSmallerReferenceEvent r (r+12) k₀ d (2*αRef) ρ₀ (1/100)
      (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) εAbsP ζAbsP βconfigP βCommonP εRef (kappa/2)
      δFixed δFixed δFixed δFixed δFixed δFixed δFixed δFixed εFixed ζFixedBal δFixed δFixed δFixed δFixed δFixed δFixed
      (2*vsizeHost) aParent bParent eParent 0 P D vsizeHost βQ ε Q π hpres (Q.length-1) (1/100)
      (ρHost*(1/100)/2) (ρHost*(1/100)/2/(((r+4):ℕ):ℝ)) qAssigned sAssigned false false weightParent weightActive
      (markedExpandedActualSelected π d z)
  let ExpandedGood:=fun z:MarkedExpandedActualOutcome (U:=Fin q) π d=>
    LongExpandedGlobalTests P π d ζret p₁ k₁ p₂ k₂ udens qAssigned z
  let Relative:=fun z:MarkedExpandedActualOutcome (U:=Fin q) π d=>
    ∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) (Q.extendedIndices 1) v).card:ℝ)≤
      (active*ε/320)*((Q.extendedVertices 1).card:ℝ)
  let aOrd:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
  let γOrd:=min (epsOrd/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
  let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16
  have hRetCopy:=hRet
  obtain ⟨hζretPos,hζlocalPos,hηBalancePos,hκauxPos,hζretS,hζretC,hζretθ,hζlocalCap,hζretLocal,
    hηBalanceS,hηBalanceC,hκauxS,hκauxRet,hκauxBalance,hRetRest⟩:=hRetCopy
  have hcutCore : (1/(((r+4):ℝ)+1))/(d:ℝ)≤θ := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hcut'
  have hcutHostCore : 5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hcutHost
  have hCore0 := first_vortex_universal_core_factor_seed_from_joint_threshold_probability
    αMatch lam lamAssign ε δold δlocal δglobal θ epsOrd ξResidual ρ₀ bmatch ξClassOrd ζret d K r
    ζOrd rho δLoss εInner eta eRob cap chainCap active ηBalance κPack βfinal Nchain hChain Nprep hPrep
  have hCore1 := hCore0 n (hChainHost.trans hNHost) (hPrepHost.trans hNHost)
    (Fin q) P π D vsizeHost βQ Q hreg hDnat hρhiHost hρloHost hDlo' hDhi' (lt_of_lt_of_le (by decide : 0<1) hvsizeHost)
    F hF Allowed hAllowed hclass hcutCore hcutHostCore hnoshort hεMatch hlamα
  have hCore2 := hCore1 aOrd γOrd ξSeed ΔSeed rfl rfl hζOrdE hξSeedResidual hζOrdSeed hepsOrd1 hζretθ hζretPos.le
    τHost A BM hBM weight hwK BO hBO w hw0 hwupper ζret βList tSeed τHost (le_refl _) hτHost.le
  have hCore3 := hCore2 gammaLoss sigmaLoss extra gammaStep sigmaStep hγBudget hσBudget (2*vsizeHost) aRob bRob eRob 0 (Q.length-1) eRob εRob ζCorr ξCorr
    (le_refl _) (Nat.sub_add_cancel Q.length_pos) hpres hξCorr.le (hbudget n) hεRob (le_refl _)
    (2*αMatch) ρreserve (by ring) (hReserveScale n hNreserve) (le_refl _)
    (by simpa using hq) hεδglobal hU hρreserve.le hreserveBudget hζOrdResidual
  have hCore4 := hCore3 (r+12) (by clear * - r; omega) (2*vsizeHost) a₀ b₀ e₀ aRob bRob eRob 0 ρHost (by dsimp [ρHost]; exact lt_of_lt_of_le hρ₀ hρloHost) hsize
    β βCommon εAbs εRob ζRob εRef (kappa/2) (min αRef (1/2:ℝ)/2)
      (1/(200*((r+4:ℕ):ℝ))) ζret εFixed ζFixedBal εNbr 1 (successorWeightUpper k₀ ((2*αRef)/4))
      1 1 1 1 ρ₀ (1/100) (ρ₀/(800*((r+4:ℕ):ℝ))) δFixed (by positivity) levelWeight
    κaux κ hηBalancePos hκauxPos hκ.le hκaux' hεRefEq hεNbr.le hεNbrCap hκauxBalance hκauxRet
    εStable ζStable capStable (2*vsizeHost) aStable bStable eStable 0 hζStable.le
    ∅ μ (fun _=>True) ExpandedGood ParentGood Relative (1-(36*(ε₀+6*ηEvent)+ηEvent))
  have hCore := hCore4 (by
      apply hProb.trans
      apply finiteLaw_probability_mono
      intro z hz
      obtain ⟨⟨hPrior,hParent,hExpanded,hStable,hCorrection,hGood,hMatching,hBoundary⟩,hRelative⟩:=hz
      exact ⟨⟨hPrior,True.intro,hExpanded,hStable,hCorrection,hGood,hMatching,hParent,hBoundary⟩,hRelative⟩)
  let NGeom : ℕ→ℕ:=fun _=>Ngeom
  have hNGeom : ∀j,1≤j→1≤NGeom j := by intro j hj;exact hNgeom
  have hSpecial := @first_vortex_protected_preparation_from_fixed_reserve_seed_probability_fin n K q (inferInstance : Nonempty (Fin n))
  have hFactor0 := hSpecial P π d r D vsizeHost βQ ε Q hpres active εStable eStable F hF θ
  have hFactor1 := hFactor0 k₀ NI Kgeom aParent bParent eParent NGeom hNGeom αRef ρ₀ δFixed εFixed ζFixedBal εAbsP ζAbsP βconfigP βCommonP εRef
    betaA betaRec kappa ξGeom thetaDeep omegaInner xiDeep etaBal (deltaLevel/2) etaLevel deltaI hIcut
  have hFactor2 := hFactor1 href hρ₀ hρloHost hkappa hX hthetaDeep hEtaLevel hd2 hε hXiDeep.le hXiScale htstarBound hDeepSource
  have hFactor3 := hFactor2 δFixed zetaCfg ζCut capOne capTwo hAtSmall hbetaCommon hRecA hεRefMax hβquarter hIcutPos.le hEtaBal
    hδIα hδIk hδIt hIcutAlpha hδFixedCut hIcutTime
  have hFactor4 := hFactor3 hn0 hU hDnat hDlo' hρhiHost hzeta hCycleFixed hPathFixed hRecTime hactiveTransfer hd2 hnoshort
  have hFactor5 := hFactor4 aOrd γOrd epsOrd ζOrd βList lamAssign δlocal δglobal αMatch bmatch ξResidual weight w
    a₀ b₀ e₀ aRob bRob eRob 0 (r+12)
  have hFactor6 := hFactor5 β βCommon εAbs εRob ζRob εRef ζret εNbr 1 (successorWeightUpper k₀ ((2*αRef)/4)) 1 1 1 1 δFixed
    (lt_of_lt_of_le (by decide : 0<3) hK3) hθpos.le (by linarith only [hθone]) hγOrd.le hε1.le hvsizeHost
  have hFactor7 := hFactor6 s c ζret ζlocal ηBalance κaux cap capStable hRet hactive hcap hcapStable hactiveGlobal hactiveLocal hCapParent
  have hFactor8 := hFactor7 ξClassOrd gammaLoss sigmaLoss rho eta κPack hεHost gammaStep sigmaStep hGammaStep hSigmaStep
    gammaCore sigmaCore extraCore hGammaSplit hSigmaSplit Nbudget (le_refl _) hNbudget μ
    (1-(36*(ε₀+6*ηEvent)+ηEvent))
  have hFactor := hFactor8 (by
      apply hCore.trans
      apply finiteLaw_probability_mono
      intro z hz
      obtain ⟨⟨hPrior,_,hExpanded,_,_,_,hParent,_⟩,_,D₀,C,_,_,_,hSeed,_⟩:=hz
      refine ⟨weightParent,weightActive,levelWeight,hParentW,hActiveW,?_,hPrior,hParent,hExpanded,D₀,C,hSeed⟩
      exact hGeo _ (Nat.sub_lt Q.length_pos (by decide)))
    hStepsAt hεStableBound
  have hTransferred := long_assigned_preparation_probability_transfer_budget_mono hn0 P F hF Allowed hAllowed π d r hd2 hm'
    (Q.extendedVertices 1) ξClassOrd eRob Bfinal (le_max_left _ _) K (lt_of_lt_of_le (by decide : 0<3) hK3) θ ρ₀ ρHost (D:ℝ) hθpos.le hθone
    hρ₀ hρloHost hρhiHost hDreal hsize hcut' hclass (fun ω=>ν (f ω))
    (1-(36*(ε₀+6*ηEvent)+ηEvent)) hFactor
  have hInner : ((Q.extendedVertices 1).card:ℝ)≤ε*(n:ℝ) := by
    simpa only [Fintype.card_fin] using Q.first_inner_vertex_size_upper hε.le
  have hεmax : ε≤εmax:=hεHost.trans (hEditCap αRef hrefAlpha)
  have hFinal := long_preparation_final_bounds (Q.extendedVertices 1) ε εmax χTarget
    (36*(ε₀+6*ηEvent)+ηEvent) _ hInner hεmax hχBudget hTransferred
  have hρeq : ρHost=ρOriginal := by
    simp only [ρHost,ρOriginal,initialIndexDensity,Fintype.card_fin]
  have hdec : longAssignedPreparationTransferBudgetFin n=instDecidableEqFin n :=
    Subsingleton.elim _ _
  rw [hdec] at hFinal
  refine ⟨Q.extendedVertices 1,hFinal.1,?_⟩
  simpa only [hρeq] using hFinal.2
-- For the later host-density premises, use first_vortex_seed_density_hierarchy r ρ₀ hρ₀ hρ₀one,
-- specialize its final forall to the actual density and tstar, and rewrite the three witness equalities;
-- the parent-k expression only needs associativity/commutativity of multiplication and division.

end Oberwolfach
