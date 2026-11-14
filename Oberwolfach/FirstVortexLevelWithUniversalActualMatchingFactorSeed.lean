module

public import Oberwolfach.FirstVortexLevelWithUniversalActualMatching
public import Oberwolfach.FirstVortexReadyCallerWithUniversalActualMatchingFactorSeed

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexLevelWithUniversalActualMatchingFactorSeed
    (r k₀ Kgeom:ℕ) (α ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε ζRob:ℝ)
    (hα:0<α) (hρ:0<ρ₀) (hζ:0<zetaCfg)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate αMatch:ℝ)
    (β βCommon εAbs εRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεAbs:ε≤εAbs) (hεRob:ε≤εRob)
    (hεsmall:ε≤min ((min α (1/2:ℝ)/2/2)*(ρ₀/(800*((r+4:ℕ):ℝ)))) (1/(200*((r+4:ℕ):ℝ)))/128)
    (hεHost:ε≤(2*α)/100000) (hm:7≤(r+4))
    (htstarBound:1/(200*((r+4:ℕ):ℝ))≤(1/100)/(((r+4):ℕ):ℝ)) (bmatch ρreserve:ℝ):Prop :=
    let gamma:=α/16
    let pA0:=ρ₀/400
    let omega₀:=ρ₀/8
    let t₀:=1/(200*((r+4:ℕ):ℝ))
    let p0:=ρ₀/(800*((r+4:ℕ):ℝ));
    ∃ omegaInner xiDeep:ℝ, 0<omegaInner ∧ omegaInner≤1 ∧ 0<xiDeep ∧
      omegaInner≤ε/8 ∧ omegaInner≤ρ₀*ε/64 ∧ ε^2≤xiDeep ∧ xiDeep≤ξ ∧
      (4*(Kgeom:ℝ)+(3*r+50:ℕ))*xiDeep≤kappa/2 ∧
      (∀ rho t:ℝ,ρ₀≤rho → t₀≤t → (1+2/rho)*xiDeep≤t*omegaInner/32) ∧
    let alphaInner:=α/8;
    ∃ betaExt epsilonExt betaRec zetaCommon:ℝ,0< betaExt ∧ 0<epsilonExt ∧ 0<betaRec ∧ 0<zetaCommon ∧ zetaCommon≤kappa/4 ∧
    betaRec≤betaExt ∧ betaRec≤betaA ∧ betaRec≤t₀/4 ∧
    3*betaRec≤markedLocalCycleCoefficient r α (t₀/2) p0-(r+5:ℕ)*zetaCfg ∧
    3*betaRec≤markedLocalPathCoefficient r α (t₀/2) p0-(r+4:ℕ)*zetaCfg ∧
    ∃ gammaMax:ℝ,0<gammaMax ∧ let gammaCap:=gammaMax;
    ∃ gammaStep:ℝ,0<gammaStep ∧ gammaStep≤gammaMax ∧ gammaStep≤gammaCap ∧ let iota:=ε/4; let aLo:=aLoA; let B:=BA;        
    ∃ η ηEnd ζ ζD pmax:ℝ,∃ hη:0<η,   0<ηEnd∧   0<ζ∧   0<ζD∧   0< pmax∧   pmax≤   1/8∧   
    let p:=min pmax (1/2:ℝ);            ∃ θ:ℝ,0<θ∧   
    ∃ delta:ℝ,0< delta∧   let x:=delta/2; 0<x ∧ x≤delta ∧    
    let pstarLocal:=ρ₀*t₀/2
    let Cparent:=11*(((r+4:ℕ):ℝ)+1)^4*(2*BA/pstarLocal^(2*(r+4)+1))
    let Clocal:=5*(((r+4:ℕ):ℝ)+1)^4*(2*BA/pstarLocal^(2*(r+4)+1));
    ∃ sigmaMax:ℝ,0<sigmaMax ∧
    ∃ sigmaStep gammaLoss sigmaLoss extra ζCorr:ℝ,
      0<sigmaStep ∧ sigmaStep≤sigmaMax ∧ 0<gammaLoss ∧ gammaLoss≤gammaCap ∧ 0<sigmaLoss ∧ 0<extra ∧
      gammaLoss+extra=gammaStep ∧ sigmaLoss+extra=sigmaStep ∧ 0<ζCorr ∧ ζCorr≤ζRob ∧
      (∀ ξCorr:ℝ,16*((((r+4):ℕ):ℝ)+1)*ξCorr≤ζCorr→∀n:ℕ,
        6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*n)≤min (gammaLoss*n) (sigmaLoss*n)) ∧
      (∀ e:ℕ,∃ Nhost:ℕ,∀ n≥Nhost,(e:ℝ)≤extra*n) ∧
    let omegaI:=ρ₀/16;
    ∃ etaBal:ℝ,0<etaBal ∧
      FirstVortexReadyCallerWithUniversalActualMatchingFactorSeed r k₀ α ρ₀ zetaCfg η etaBal x hα hρ hζ hη
        cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate αMatch ε
        β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
        hε hε1 hεAbs hεRob hεsmall hεHost hm htstarBound bmatch ρreserve ∧ ∃ NI:ℕ,
      ∃ tolRef ζActive τParent tolParent ζParent τ tolLocal ζLocal rowErr ζRow epsBal ζBal:ℝ,
        0<tolRef ∧ tolRef≤1 ∧ 0<ζActive ∧ ζActive≤1 ∧
        tolRef+(r+12:ℕ)*ζActive≤kappa/4 ∧ tolRef+(r+12:ℕ)*ζActive≤x/2 ∧ ζActive≤kappa/4 ∧
        0<τParent ∧ τParent≤1 ∧ 0<tolParent ∧ tolParent≤1 ∧ 0<ζParent ∧ ζParent≤1 ∧
        τParent+tolParent+Cparent*ζParent≤kappa/4 ∧ τParent+tolParent+Cparent*ζParent≤thetaDeep/4 ∧
        0<τ ∧ τ≤1 ∧ 0<tolLocal ∧ tolLocal≤1 ∧ τ+tolLocal≤η/8 ∧
        0<ζLocal ∧ ζLocal≤1 ∧ τ+tolLocal+Clocal*ζLocal≤η/4 ∧
        0<rowErr ∧ rowErr≤1 ∧ 0<ζRow ∧ ζRow≤1 ∧ rowErr+ζRow≤t₀/8 ∧
        0<epsBal ∧ epsBal≤1 ∧ 0<ζBal ∧ ζBal≤1 ∧
        epsBal+((r+4)+2:ℕ)*ζBal≤etaBal ∧ epsBal+((r+4)+2:ℕ)*ζBal≤x/2 ∧
        (∀ ε Cwide:ℝ,0<ε→0≤Cwide→∃ ζWide:ℝ,0<ζWide ∧ ζWide≤1 ∧
          τ+tolLocal+Cwide*(4/ε)*ζWide≤η/4) ∧
    ∃ ζWide δparent:ℝ,0<ζWide ∧ ζWide≤1 ∧ 0<δparent ∧
      δparent≤zetaCfg ∧ δparent≤zetaCommon ∧ δparent≤ζCut ∧ δparent≤kappa/4 ∧
      3*betaA≤markedLocalCycleCoefficient r α (t₀/2) p0-(r+5:ℕ)*δparent ∧
      3*betaA≤markedLocalPathCoefficient r α (t₀/2) p0-(r+4:ℕ)*δparent ∧
      δparent+(r+12:ℕ)*δparent≤kappa/4 ∧ δparent+(r+12:ℕ)*δparent≤x/2 ∧
      δparent+δparent+Cparent*δparent≤kappa/4 ∧ δparent+δparent+Cparent*δparent≤thetaDeep/4 ∧
      δparent+δparent+Clocal*δparent≤η/4 ∧
      δparent+δparent+Clocal*(4/ε)*δparent≤η/4 ∧
      δparent+δparent≤t₀/8 ∧ 2*hIcut≤t₀/8-δparent ∧
    FirstVortexParentAlignedRates r δparent zetaCfg kappa x thetaDeep η t₀ ((1/100)/(((r+4):ℕ):ℝ)) Cparent Clocal ε etaBal epsBal ζBal ∧
    FirstVortexActualParentAlignedRates r ρ₀ (1/100) t₀ BA δparent zetaCfg kappa x thetaDeep η ε etaBal epsBal ζBal betaA
      (markedLocalCycleCoefficient r α (t₀/2) p0) (markedLocalPathCoefficient r α (t₀/2) p0) ∧
    ∀ d:ℕ,1≤d → ∃ N:ℕ,1≤N ∧
    ∀ rho omega t:ℝ,ρ₀≤rho → rho≤1 → omega₀≤omega → omega≤1 → t₀≤t → (r+4:ℝ)*t≤1 →
    pA0≤rho*(r+4:ℝ)*t/2 → p0≤rho*(r+4:ℝ)*t/2 → p0≤rho*t/2 → p0≤t →
    ∀ (Gamma Color : Type) [Fintype Gamma] [Fintype Color],
    ∀ level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota betaRec aLo B η x omegaI hIcut deltaI etaBal,
      MarkedReferenceLevelStepProperty level (gammaLoss+extra) (sigmaLoss+extra)
theorem first_vortex_level_with_universal_actual_matching_factor_seed
    (r k₀ Kgeom:ℕ) (α ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε ζRob:ℝ)
    (hα:0<α) (hρ:0<ρ₀) (hζ:0<zetaCfg)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate αMatch:ℝ)
    (β βCommon εAbs εRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεAbs:ε≤εAbs) (hεRob:ε≤εRob)
    (hεsmall:ε≤min ((min α (1/2:ℝ)/2/2)*(ρ₀/(800*((r+4:ℕ):ℝ)))) (1/(200*((r+4:ℕ):ℝ)))/128)
    (hεHost:ε≤(2*α)/100000) (hm:7≤r+4)
    (htstarBound:1/(200*((r+4:ℕ):ℝ))≤(1/100)/(((r+4):ℕ):ℝ)) (bmatch ρreserve βListInit εLevelInit hostCapInit:ℝ)
    (hInitial:FirstVortexInitialMatchingVortexRates ρ₀ δglobal βListInit βfinal εLevelInit εInner εAbs εRob
      (min α (1/2:ℝ)/2) (ρ₀/(800*((r+4:ℕ):ℝ))) (1/(200*((r+4:ℕ):ℝ))) hostCapInit bmatch αMatch ε)
    (hρreserve:0≤ρreserve)
    (hListMargin:βfinal+2*ρreserve≤((min (2*α) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/2)
    (hζStable:0≤ζStable)
    (hReserveSize:∀e:ℕ,∃N:ℕ,∀n:ℕ,N≤n→(e:ℝ)≤ρreserve*n)
    (hLevel:FirstVortexLevelWithUniversalParentChain r k₀ Kgeom α ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε ζRob hα hρ hζ
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate αMatch
      β βCommon εAbs εRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      hε hε1 hεAbs hεRob hεsmall hεHost hm htstarBound bmatch):
    FirstVortexLevelWithUniversalActualMatchingFactorSeed r k₀ Kgeom α ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε ζRob hα hρ hζ
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate αMatch
      β βCommon εAbs εRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      hε hε1 hεAbs hεRob hεsmall hεHost hm htstarBound bmatch ρreserve :=by
  obtain ⟨omegaInner,xiDeep,hω,hωone,hxi,hωε,hωρ,hεxi,hxiξ,hxiκ,hbound,h⟩:=hLevel
  refine ⟨omegaInner,xiDeep,hω,hωone,hxi,hωε,hωρ,hεxi,hxiξ,hxiκ,hbound,?_⟩
  obtain ⟨betaExt,epsilonExt,betaRec,zetaCommon,hbe,hee,hbr,hzc,hzck,hbre,hbra,hbrt,hbrc,hbrp,gammaMax,hgm,h⟩:=h
  refine ⟨betaExt,epsilonExt,betaRec,zetaCommon,hbe,hee,hbr,hzc,hzck,hbre,hbra,hbrt,hbrc,hbrp,gammaMax,hgm,?_⟩
  obtain ⟨gammaStep,hgs,hgmax,hgcap,η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ0,hζD,hpmax,hpmax8,θ,hθ,delta,hδ,hx,hxδ,h⟩:=h
  refine ⟨gammaStep,hgs,hgmax,hgcap,η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ0,hζD,hpmax,hpmax8,θ,hθ,delta,hδ,hx,hxδ,?_⟩
  obtain ⟨sigmaMax,hsmax,sigmaStep,gammaLoss,sigmaLoss,extra,ζCorr,hs,hsle,hg,hgle,hsl,hextra,hgeq,hseq,hcorr,hcorrRob,hbudget,hhost,etaBal,hηBal,hTransfer,hRest⟩:=h
  refine ⟨sigmaMax,hsmax,sigmaStep,gammaLoss,sigmaLoss,extra,ζCorr,hs,hsle,hg,hgle,hsl,hextra,hgeq,hseq,hcorr,hcorrRob,hbudget,hhost,etaBal,hηBal,?_,hRest⟩
  exact first_vortex_ready_caller_with_universal_actual_matching_factor_seed r k₀ α ρ₀ zetaCfg η etaBal (delta/2) hα hρ hζ hη
    cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate αMatch ε
    β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
    hε hε1 hεAbs hεRob hεsmall hεHost hm htstarBound bmatch ρreserve βListInit εLevelInit hostCapInit
    hInitial hρreserve hListMargin hζStable hReserveSize hTransfer
end Oberwolfach
