module

public import Oberwolfach.FirstVortexSharedVortexTailTransferReady
public import Oberwolfach.FirstVortexLevelChosenForCaller

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

def FirstVortexSharedVortexTailLevelReady (r k₀:ℕ) (αRef ρ₀:ℝ) (hα:0<αRef) (hρ₀:0<ρ₀):Prop :=
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
      FirstVortexSelectorActualHostCoreLateThresholdTail r (r+12) k₀ 1 αRef sstar ω γRich tstar kstar ρ₀ hρ₀
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
      FirstVortexLevelChosenForCaller r Kgeom αRef ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε ζRob ∧
      FirstVortexInitialTransferAfterRates r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate αMatch ε




theorem first_vortex_shared_vortex_level_ready
    (r k₀:ℕ) (αRef ρ₀:ℝ) (hα:0<αRef) (hρ₀:0<ρ₀)
    (h:FirstVortexSharedVortexTailTransferReady r k₀ αRef ρ₀ hα hρ₀):
    FirstVortexSharedVortexTailLevelReady r k₀ αRef ρ₀ hα hρ₀ :=by
  obtain ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,
    εStable,ζStable,capStable,hεStable,hζStable,hcapStable,hSelector,hBA,
    βfinal,ρreserve,hβfinal,hβone,hβlist,hρreserve,hreserveList,hreserveSize,
    zetaCfg,betaA,hzeta,hbetaA,hbetaCfg,hbetaCommon,hcycle,hpath,
    Kgeom,hKgeom,kappa0,ξ,thetaDeep,kappa,hkappa0,hξ,htheta,hkappa,hkappaLe,
    ζCut,hIcut,εLevel,deltaI,hζcut,hζcut1,hζcutT,hIcut0,hIcutA,hIcutT,
    hεLevel,hεCut,hεξ,hεκ,hεα,hεone,hδI,hδIone,hδIα,hδIk,hδIt,
    cap,hcap,hcapStable',hparent,
    rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hGlobal,
    bmatch,αMatch,ε,hInitial,hεStable',hεHost,hLevel,hTransfer⟩:=h
  have hε:0<ε:=hInitial.2.2.2.2.2.1
  have hWeights:=successorWeightConstants_pos k₀ (αRef/4) (by positivity)
  have hChosen:=first_vortex_level_chosen_for_caller r Kgeom αRef ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI
    (successorWeightLower k₀ (αRef/4)) (successorWeightUpper k₀ (αRef/4)) ε ζRob hα hρ₀ hWeights.1 hWeights.2.le hε hζRob hLevel
  refine ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,
    εStable,ζStable,capStable,hεStable,hζStable,hcapStable,hSelector,hBA,
    βfinal,ρreserve,hβfinal,hβone,hβlist,hρreserve,hreserveList,hreserveSize,
    zetaCfg,betaA,hzeta,hbetaA,hbetaCfg,hbetaCommon,hcycle,hpath,
    Kgeom,hKgeom,kappa0,ξ,thetaDeep,kappa,hkappa0,hξ,htheta,hkappa,hkappaLe,
    ζCut,hIcut,εLevel,deltaI,hζcut,hζcut1,hζcutT,hIcut0,hIcutA,hIcutT,
    hεLevel,hεCut,hεξ,hεκ,hεα,hεone,hδI,hδIone,hδIα,hδIk,hδIt,
    cap,hcap,hcapStable',hparent,
    rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hGlobal,
    bmatch,αMatch,ε,hInitial,hεStable',hεHost,hChosen,hTransfer⟩
end Oberwolfach
