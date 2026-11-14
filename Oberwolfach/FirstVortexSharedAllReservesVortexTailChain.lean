module

public import Oberwolfach.FirstVortexLevelWithPreparedTailLateLoss
public import Oberwolfach.FirstVortexSharedAllReservesLateHostBothLevelTails
public import Oberwolfach.FirstVortexCallerLocalLateCaps
public import Oberwolfach.FirstVortexSharedProbabilitySelectorLevelReserveParametersExactMargin
public import Oberwolfach.FirstVortexLevelAfterVortexExactMargin
public import Oberwolfach.FirstVortexGlobalRatesContinuation
public import Oberwolfach.FirstVortexInitialMatchingVortexRates
public import Oberwolfach.FirstVortexExactParentCapBound

@[expose] public section
/-! Choose one vortex scale after the shared parent selector, uniform level
constants, terminal reserve and exact global cap have been fixed. -/
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

theorem first_vortex_shared_all_reserves_vortex_tail_chain
    (αRef ρ₀:ℝ) (hα:0<αRef) (hαCap:2*αRef≤1) (hρ₀:0<ρ₀) (hρ₀one:ρ₀≤1):
    ∃c₀:ℕ,∀r:ℕ,2≤r→c₀≤r+5→∀k₀:ℕ,
      r+4+1=(k₀+2)*2→successorCycleRatio k₀+αRef/2≤1/2+αRef→
    let sstar:ℝ:=1/100
    let tstar:ℝ:=1/(200*((r+4:ℕ):ℝ))
    let kstar:ℝ:=ρ₀/(800*((r+4:ℕ):ℝ))
    let ω:ℝ:=ρ₀/4
    let γRich:ℝ:=min αRef (1/2:ℝ)/2
    let aLoA:=successorWeightLower k₀ (αRef/4)
    let BA:=successorWeightUpper k₀ (αRef/4)
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    ∃β βCommon εAbs εRob ζRob δAbs:ℝ,0<β ∧ 0<βCommon ∧ 0<εAbs ∧ 0<εRob ∧ 0<ζRob ∧ 0<δAbs ∧
    ∃εAbsP ζAbsP δAbsP βconfigP βCommonP:ℝ,
      0<εAbsP ∧ 0<ζAbsP ∧ 0<δAbsP ∧ 0<βconfigP ∧ 0<βCommonP ∧
    ∃εStable ζStable capStable:ℝ,0<εStable ∧ 0<ζStable ∧ 0<capStable ∧
      aLoA≤successorWeightLower k₀ ((2*αRef)/4) ∧ successorWeightUpper k₀ ((2*αRef)/4)≤BA ∧
      FirstVortexNamedAllReservesLateHostRetentionTail r (r+12) k₀ 1 αRef sstar ω γRich tstar kstar ρ₀ hρ₀
        β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable ∧
      FirstVortexUniformLevelActualParentTail r αRef ρ₀ hα hρ₀ βconfigP βCommonP
        (successorWeightLower k₀ ((2*αRef)/4)) (successorWeightUpper k₀ ((2*αRef)/4)) ∧
    ∃βfinal ρreserve:ℝ,0<βfinal ∧ βfinal≤1 ∧ βfinal≤βList/4 ∧ 0<ρreserve ∧
      βfinal+2*ρreserve≤βList/2 ∧
      (∀e:ℕ,∃N:ℕ,∀n:ℕ,N≤n→(e:ℝ)≤ρreserve*n) ∧
    ∃zetaCfg:ℝ,∃hzeta:0<zetaCfg,∃betaA:ℝ,0<betaA ∧ betaA≤βconfigP ∧ betaA≤βCommonP ∧
      3*betaA≤markedLocalCycleCoefficient r αRef (tstar/2) kstar-(r+5:ℕ)*zetaCfg ∧
      3*betaA≤markedLocalPathCoefficient r αRef (tstar/2) kstar-(r+4:ℕ)*zetaCfg ∧
    ∃Kgeom:ℕ,0<Kgeom ∧ ∃kappa0 ξ thetaDeep kappa:ℝ,0<kappa0 ∧ 0<ξ ∧ 0<thetaDeep ∧ 0<kappa ∧ kappa≤kappa0 ∧
    ∃ζCut hIcut εLevel deltaI:ℝ,0<ζCut ∧ ζCut≤1 ∧ ζCut≤tstar/16 ∧
      0<hIcut ∧ 2*hIcut≤αRef*kstar/4 ∧ 2*hIcut≤tstar/8-ζCut ∧
      0<εLevel ∧ εLevel≤hIcut ∧ 4*εLevel≤ξ ∧ εLevel≤kappa ∧ εLevel≤αRef/8 ∧ εLevel≤1/8 ∧
      0<deltaI ∧ deltaI<1/4 ∧ deltaI≤αRef/32 ∧ deltaI≤kstar/32 ∧ 2*deltaI≤tstar/8 ∧
    ∃cap:ℝ,0<cap ∧ cap≤capStable ∧ FirstVortexExactParentCapBound r αRef ρ₀ kappa zetaCfg thetaDeep BA cap hα hρ₀ ∧
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ,
      FirstVortexAmbientGlobalData r ρ₀ cap (βfinal/2) rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate ∧
      δglobal≤(βfinal/200)^2 ∧
    ∃bmatch αMatch ε δold δlocal:ℝ,
      αMatch≤αRef ∧
      FirstVortexInitialMatchingVortexRates ρ₀ δglobal βList βfinal (min εLevel (min εStable ((2*αRef)/100000))) εInner εAbs εRob γRich kstar tstar (βList/32) bmatch αMatch ε ∧
      ε≤εStable ∧ ε≤(2*αRef)/100000 ∧
      0<δold ∧ δold≤1 ∧ δold≤δglobal ∧ δold<δlocal ∧ δlocal=2*δold ∧ δlocal≤δglobal ∧
      ∃(hm:7≤r+4) (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ)),
      FirstVortexLevelWithPreparedTailLateLoss r k₀ Kgeom αRef ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε ζRob hα hρ₀ hzeta
        cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate αMatch δold δlocal bmatch
        (r+12) 1 sstar ω γRich tstar kstar β βCommon εAbs εRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable hm htstarBound :=by
  obtain ⟨c₀,hShared⟩:=first_vortex_shared_all_reserves_late_host_both_level_tails αRef ρ₀ hα hαCap hρ₀ hρ₀one
  refine ⟨c₀,?_⟩
  intro r hr hrc k₀ hlen hmargin sstar tstar kstar ω γRich aLoA BA βList
  obtain ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,
    εStable,ζStable,capStable,hεStable,hζStable,hcapStable,hLower,hUpper,hSelector,hLevel,hLevelTwo,_hReserve⟩:=hShared r hr hrc k₀ hlen hmargin
  have hContract:=first_vortex_original_prepared_late_cap_and_local_contract r ρ₀ αRef hρ₀ hρ₀one hα (by omega)
  obtain ⟨βfinal,ρreserve,hβfinal,hβfinal1,hβList,hρreserve,hresBudget,hresHost,hCapFor⟩:=hContract
  obtain ⟨zetaCfg,betaA,hzeta,hbetaA,hbetaConfig,hbetaCommon,hcycle,hpath,Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hTheta,hLevel⟩:=hLevel
  let kappa:=min kappa0 (1:ℝ)/2
  have hkappa:0<kappa:=by dsimp [kappa];positivity
  have hkappaCap:kappa≤kappa0:=by dsimp [kappa];have hh:=min_le_left kappa0 (1:ℝ);linarith
  obtain ⟨ζCut,hIcut,εLevel,deltaI,hCut,hCutCap,hCutSmall,hi,hiprod,hispoke,he₀,hecut,heξ,heκ,heα,he8,hδ,hδsmall,hδα,hδp,hδt,hLevel⟩:=hLevel kappa hkappa hkappaCap
  have hBA:0≤BA:=by
    dsimp [BA]
    exact (successorWeightConstants_pos k₀ (αRef/4) (by positivity)).2.le
  obtain ⟨cap,hcap,hcapExact,hcapStableBound,_hGlobal,hLevel⟩:=hLevel hzeta hTheta hBA capStable βfinal hcapStable hβfinal
  have hExact:FirstVortexExactParentCapBound r αRef ρ₀ kappa zetaCfg thetaDeep BA cap hα hρ₀:=
    ⟨hkappa,hzeta,hTheta,hBA,hcapExact⟩
  obtain ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hAmbient,hδbound,hLater⟩:=hCapFor cap hcap
  have hγ:0<γRich:=by dsimp [γRich];positivity
  have hkstar:0<kstar:=by dsimp [kstar];positivity
  have htstar:0<tstar:=by dsimp [tstar];positivity
  have hList:0<βList:=by dsimp [βList];positivity
  obtain ⟨αMatch,ε,δold,δlocal,bmatch,hαMatch,hExtra,hRates,hδold,hδold1,hδoldGlobal,hδgap,hδlocal,hlocalGlobal,hLocal⟩:=
    hLater αRef (min εLevel (min εStable ((2*αRef)/100000))) εAbs εRob γRich kstar tstar (βList/32) (βList/32)
      hα (by positivity) hεAbs hεRob hγ hkstar htstar (by positivity) (by positivity)
  have hRatesCopy:=hRates
  obtain ⟨_,_,_,_,_,hε,_,hεLevel,_,_,_,_,_,_,_,_,_,_,_⟩:=hRates
  have hεLevel':ε≤εLevel:=hεLevel.trans (min_le_left _ _)
  have hεRest:=hεLevel.trans (min_le_right _ _)
  have hεStableBound:ε≤εStable:=hεRest.trans (min_le_left _ _)
  have hεHostRef:ε≤(2*αRef)/100000:=hεRest.trans (min_le_right _ _)
  have hLevelAfter:FirstVortexLevelAfterVortexExactMargin r Kgeom αRef ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε:=hLevel ε hε hεLevel'
  have hLocalAfter:FirstVortexCallerLocalLateCaps r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate αMatch ε δold δlocal bmatch:=hLocal
  have haLo:0<aLoA:=by
    dsimp [aLoA]
    exact (successorWeightConstants_pos k₀ (αRef/4) (by positivity)).1
  have hChosen:=first_vortex_level_chosen_for_caller r Kgeom αRef ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε ζRob hα hρ₀ haLo hBA hε hζRob hLevelAfter
  have hAmbientCopy:=hAmbient
  obtain ⟨hrho,heta,_,_,_,_,_,_,_,hetaR,_⟩:=hAmbientCopy
  have hm:7≤r+4:=by omega
  have htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ):=by
    dsimp [tstar]
    have hrpos:(0:ℝ)≤((r+4:ℕ):ℝ):=by positivity
    have hh:=div_le_div_of_nonneg_right (show (1:ℝ)/200≤1/100 by norm_num) hrpos
    convert hh using 1 <;> ring
  have hExplicit:=first_vortex_level_with_prepared_tail_late_loss r k₀ Kgeom αRef ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε ζRob hα hρ₀ hzeta
    cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate αMatch δold δlocal bmatch
    (r+12) 1 sstar ω γRich tstar kstar β βCommon εAbs εRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable hm htstarBound hζRob
    βList (min εLevel (min εStable ((2*αRef)/100000))) (βList/32) hRatesCopy hδold hδold1 hρ₀one hrho heta hetaR hβfinal hβfinal1 hSelector hChosen hLocalAfter
  exact ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,
    εStable,ζStable,capStable,hεStable,hζStable,hcapStable,hLower,hUpper,hSelector,hLevelTwo,
    βfinal,ρreserve,hβfinal,hβfinal1,hβList,hρreserve,hresBudget,hresHost,
    zetaCfg,hzeta,betaA,hbetaA,hbetaConfig,hbetaCommon,hcycle,hpath,Kgeom,hKgeom,kappa0,ξ,thetaDeep,kappa,hkappa0,hξ,hTheta,hkappa,hkappaCap,
    ζCut,hIcut,εLevel,deltaI,hCut,hCutCap,hCutSmall,hi,hiprod,hispoke,he₀,hecut,heξ,heκ,heα,he8,hδ,hδsmall,hδα,hδp,hδt,
    cap,hcap,hcapStableBound,hExact,rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hAmbient,hδbound,
    bmatch,αMatch,ε,δold,δlocal,hαMatch,hRatesCopy,hεStableBound,hεHostRef,hδold,hδold1,hδoldGlobal,hδgap,hδlocal,hlocalGlobal,hm,htstarBound,hExplicit⟩
end Oberwolfach
