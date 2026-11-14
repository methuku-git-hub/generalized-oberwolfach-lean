module

public import Oberwolfach.FirstVortexSharedSelectorHighProbabilityReserve
public import Oberwolfach.FirstVortexParentAlignedWeightMonotonicity
public import Oberwolfach.FirstVortexSharedSelectorLevelReserveParametersDistinctWeights
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

theorem first_vortex_shared_vortex_high_probability_parameters
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
    let BAParent:=successorWeightUpper k₀ ((2*αRef)/4)
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    ∃β βCommon εAbs εRob ζRob δAbs:ℝ,0<β ∧ 0<βCommon ∧ 0<εAbs ∧ 0<εRob ∧ 0<ζRob ∧ 0<δAbs ∧
    ∃εAbsP ζAbsP δAbsP βconfigP βCommonP:ℝ,
      0<εAbsP ∧ 0<ζAbsP ∧ 0<δAbsP ∧ 0<βconfigP ∧ 0<βCommonP ∧
    ∃εStable ζStable capStable:ℝ,0<εStable ∧ 0<ζStable ∧ 0<capStable ∧
      FirstVortexNamedHighProbabilitySelectorTail r (r+12) k₀ 1 αRef sstar ω γRich tstar kstar ρ₀ hρ₀
        β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable ∧
    BAParent≤BA ∧
    ∃βfinal ρreserve:ℝ,0<βfinal ∧ βfinal≤1 ∧ βfinal≤βList/4 ∧ 0<ρreserve ∧
      βfinal+2*ρreserve≤βList/2 ∧
      (∀e:ℕ,∃N:ℕ,∀n:ℕ,N≤n→(e:ℝ)≤ρreserve*n) ∧
    ∃zetaCfg betaA:ℝ,0<zetaCfg ∧ 0<betaA ∧ betaA≤βconfigP ∧ betaA≤βCommonP ∧
      3*betaA≤markedLocalCycleCoefficient r αRef (tstar/2) kstar-(r+5:ℕ)*zetaCfg ∧
      3*betaA≤markedLocalPathCoefficient r αRef (tstar/2) kstar-(r+4:ℕ)*zetaCfg ∧
    ∃Kgeom:ℕ,0<Kgeom ∧ ∃kappa0 ξ thetaDeep kappa:ℝ,0<kappa0 ∧ 0<ξ ∧ 0<thetaDeep ∧ 0<kappa ∧ kappa≤kappa0 ∧
    ∃ζCut hIcut εLevel deltaI:ℝ,0<ζCut ∧ ζCut≤1 ∧ ζCut≤tstar/16 ∧
      0<hIcut ∧ 2*hIcut≤αRef*kstar/4 ∧ 2*hIcut≤tstar/8-ζCut ∧
      0<εLevel ∧ εLevel≤hIcut ∧ 4*εLevel≤ξ ∧ εLevel≤kappa ∧ εLevel≤αRef/8 ∧ εLevel≤1/8 ∧
      0<deltaI ∧ deltaI<1/4 ∧ deltaI≤αRef/32 ∧ deltaI≤kstar/32 ∧ 2*deltaI≤tstar/8 ∧
    ∃cap:ℝ,0<cap ∧ cap≤capStable ∧ FirstVortexExactParentCapBound r αRef ρ₀ kappa zetaCfg thetaDeep BAParent cap hα hρ₀ ∧
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ,
      FirstVortexGlobalRatesContinuation r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate ∧
    ∃bmatch αMatch ε:ℝ,
      FirstVortexInitialMatchingVortexRates ρ₀ δglobal βList βfinal (min εLevel (min εStable ((2*αRef)/100000))) εInner εAbs εRob γRich kstar tstar (βList/32) bmatch αMatch ε ∧
      ε≤εStable ∧ ε≤(2*αRef)/100000 ∧
      FirstVortexLevelAfterVortexExactMargin r Kgeom αRef ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε :=by
  obtain ⟨c₀,hShared⟩:=first_vortex_shared_selector_high_probability_reserve αRef ρ₀ hα hαCap hρ₀ hρ₀one
  refine ⟨c₀,?_⟩
  intro r hr hrc k₀ hlen hmargin sstar tstar kstar ω γRich aLoA BA BAParent βList
  obtain ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,
    εStable,ζStable,capStable,hεStable,hζStable,hcapStable,hSelector,hLevel,hReserve⟩:=hShared r hr hrc k₀ hlen hmargin
  obtain ⟨βfinal,ρreserve,hβfinal,hβfinal1,hβList,hρreserve,hresBudget,hresHost,hInitial⟩:=hReserve
  obtain ⟨zetaCfg,betaA,hzeta,hbetaA,hbetaConfig,hbetaCommon,hcycle,hpath,Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hTheta,hLevel⟩:=hLevel
  let kappa:=min kappa0 (1:ℝ)/2
  have hkappa:0<kappa:=by dsimp [kappa];positivity
  have hkappaCap:kappa≤kappa0:=by dsimp [kappa];have hh:=min_le_left kappa0 (1:ℝ);linarith
  obtain ⟨ζCut,hIcut,εLevel,deltaI,hCut,hCutCap,hCutSmall,hi,hiprod,hispoke,he₀,hecut,heξ,heκ,heα,he8,hδ,hδsmall,hδα,hδp,hδt,hLevel⟩:=hLevel kappa hkappa hkappaCap
  have hBA:0≤BA:=by
    dsimp [BA]
    exact (successorWeightConstants_pos k₀ (αRef/4) (by positivity)).2.le
  have hWeightCompare:BAParent≤BA:=by
    dsimp [BAParent,BA]
    apply successor_weight_upper_antitone k₀ (αRef/4) ((2*αRef)/4) (by positivity)
    linarith
  have hBAParent:0≤BAParent:=by
    dsimp [BAParent]
    exact (successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2.le
  let parentExact:=Classical.choose (marked_vortex_fixed_margin_local_correction_cap r kappa (2*αRef) (ρ₀/4) kstar kstar tstar kstar zetaCfg thetaDeep (1:ℝ)
    BAParent kstar (1:ℝ) (1:ℝ) (1:ℝ) hkappa (by positivity) (by positivity) (by dsimp [kstar]; positivity) (by dsimp [kstar]; positivity)
    (by dsimp [tstar]; positivity) hzeta hTheta (by norm_num) hBAParent (by dsimp [kstar]; positivity) (by norm_num) (by norm_num) (by norm_num))
  have hparentExact:0<parentExact:=(Classical.choose_spec (marked_vortex_fixed_margin_local_correction_cap r kappa (2*αRef) (ρ₀/4) kstar kstar tstar kstar zetaCfg thetaDeep (1:ℝ)
    BAParent kstar (1:ℝ) (1:ℝ) (1:ℝ) hkappa (by positivity) (by positivity) (by dsimp [kstar]; positivity) (by dsimp [kstar]; positivity)
    (by dsimp [tstar]; positivity) hzeta hTheta (by norm_num) hBAParent (by dsimp [kstar]; positivity) (by norm_num) (by norm_num) (by norm_num))).1
  obtain ⟨cap,hcap,hcapExact,hcapStableMin,hGlobal,hLevel⟩:=hLevel hzeta hTheta hBA (min capStable parentExact) βfinal (by positivity) hβfinal
  have hcapStableBound:cap≤capStable:=hcapStableMin.trans (min_le_left _ _)
  have hcapParent:cap≤parentExact:=hcapStableMin.trans (min_le_right _ _)
  have hExact:FirstVortexExactParentCapBound r αRef ρ₀ kappa zetaCfg thetaDeep BAParent cap hα hρ₀:=
    ⟨hkappa,hzeta,hTheta,hBAParent,hcapParent⟩
  obtain ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hAmbient,hδbound,hLater⟩:=hGlobal
  have hAmbientCopy:=hAmbient
  obtain ⟨hrho,heta,hζmax,hΔmax,hδLoss,hεInner,hδglobal,hθmax,hglobalRate,_,_,_,_,_,_,_,_,_,_,_,_⟩:=hAmbient
  have hγ:0<γRich:=by dsimp [γRich];positivity
  have hkstar:0<kstar:=by dsimp [kstar];positivity
  have htstar:0<tstar:=by dsimp [tstar];positivity
  obtain ⟨bmatch,αMatch,ε,hRates⟩:=hInitial δglobal (min εLevel (min εStable ((2*αRef)/100000))) εInner εAbs εRob γRich kstar tstar
    hδglobal (by positivity) hεInner hεAbs hεRob hγ hkstar htstar
  have hRatesCopy:=hRates
  obtain ⟨_,_,_,_,_,hε,_,hεLevel,_,_,_,_,_,_,_,_,_,_,_⟩:=hRates
  have hεLevel':ε≤εLevel:=hεLevel.trans (min_le_left _ _)
  have hεRest:=hεLevel.trans (min_le_right _ _)
  have hεStableBound:ε≤εStable:=hεRest.trans (min_le_left _ _)
  have hεHostRef:ε≤(2*αRef)/100000:=hεRest.trans (min_le_right _ _)
  have hLevelAfter:FirstVortexLevelAfterVortexExactMargin r Kgeom αRef ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε:=hLevel ε hε hεLevel'
  have hGlobalAfter:FirstVortexGlobalRatesContinuation r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:=⟨hAmbientCopy,hδbound,hLater⟩
  exact ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,
    εStable,ζStable,capStable,hεStable,hζStable,hcapStable,hSelector,hWeightCompare,
    βfinal,ρreserve,hβfinal,hβfinal1,hβList,hρreserve,hresBudget,hresHost,
    zetaCfg,betaA,hzeta,hbetaA,hbetaConfig,hbetaCommon,hcycle,hpath,Kgeom,hKgeom,kappa0,ξ,thetaDeep,kappa,hkappa0,hξ,hTheta,hkappa,hkappaCap,
    ζCut,hIcut,εLevel,deltaI,hCut,hCutCap,hCutSmall,hi,hiprod,hispoke,he₀,hecut,heξ,heκ,heα,he8,hδ,hδsmall,hδα,hδp,hδt,
    cap,hcap,hcapStableBound,hExact,rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hGlobalAfter,bmatch,αMatch,ε,hRatesCopy,hεStableBound,hεHostRef,hLevelAfter⟩
end Oberwolfach
