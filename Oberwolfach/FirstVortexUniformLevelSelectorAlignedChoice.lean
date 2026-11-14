module

public import Oberwolfach.FirstVortexUniformLevelAlignedParentChoice
public import Oberwolfach.FirstVortexActualParentToleranceAlignment

@[expose] public section
/-! The uniform level continuation also carries the exact coefficient
comparison for the parent weights selected on the matching sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexActualParentAlignedProperty
    (r:ℕ) (ρ₀ sstar tstar B δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff:ℝ):Prop :=
    let m:ℝ:=((r+4):ℕ)
    let pLevel:=ρ₀*tstar/2
    let pSelector:=ρ₀*sstar/(2*m)
    let CpLevel:=11*(m+1)^4*(2*B/pLevel^(2*(r+4)+1))
    let CpSelector:=11*(m+1)^4*(2*B/pSelector^(2*(r+4)+1))
    let ClLevel:=5*(m+1)^4*(2*B/pLevel^(2*(r+4)+1))
    let ClSelector:=5*(m+1)^4*(2*B/pSelector^(2*(r+4)+1));
    δ+((r+12:ℕ):ℝ)*δ≤κ/4→δ+((r+12:ℕ):ℝ)*δ≤x/2→
    δ+δ+CpLevel*δ≤κ/4→δ+δ+CpLevel*δ≤thetaDeep/4→
    δ+δ+ClLevel*(4/ε)*δ≤eta/4→δ+δ≤tstar/8→
    ∃δ' εBal ζBal:ℝ,0<δ' ∧ δ'≤δ ∧ 2*δ'≤ζCfg ∧
      δ'≤(κ/2)/4 ∧ δ'+((r+12:ℕ):ℝ)*δ'≤(κ/2)/4 ∧
      δ'+((r+12:ℕ):ℝ)*δ'≤(x/2)/2 ∧
      δ'+δ'+CpSelector*δ'≤(κ/2)/4 ∧ δ'+δ'+CpSelector*δ'≤(thetaDeep/2)/4 ∧
      δ'+δ'+ClSelector*(4/ε)*δ'≤(eta/2)/4 ∧
      δ'+δ'≤tstar/16 ∧ δ'+δ'≤(sstar/m)/8 ∧
      0<εBal ∧ 0<ζBal ∧ εBal≤cap₁ ∧ ζBal≤cap₂ ∧
      εBal+((r+4)+2:ℕ)*ζBal≤etaBal/2 ∧ εBal+((r+4)+2:ℕ)*ζBal≤x/4 ∧
      3*βA≤cycleCoeff-((r+5:ℕ):ℝ)*δ' ∧
      3*βA≤pathCoeff-((r+4:ℕ):ℝ)*δ'

theorem first_vortex_uniform_level_selector_aligned_choice
    (α ρ₀:ℝ) (hα:0<α) (hαCap:2*α≤1) (hρ₀:0<ρ₀) (hρ₀one:ρ₀≤1):
    let gamma:=α/8
    let pA0:=ρ₀/400
    let omega₀:=ρ₀/8;
    ∃c₀:ℕ,∀r:ℕ,2≤r→c₀≤r+5→
    let t₀:=1/(200*((r+4:ℕ):ℝ))
    let p0:=ρ₀/(800*((r+4:ℕ):ℝ));
    ∀ betaConfig betaCommon aLoA BA:ℝ,
      0<betaConfig→0<betaCommon→0<aLoA→0<BA→
    ∃ zetaCfg betaA:ℝ,0<zetaCfg ∧ 0<betaA ∧ betaA≤betaConfig ∧ betaA≤betaCommon ∧
    3*betaA≤markedLocalCycleCoefficient r α (t₀/2) p0-(r+5:ℕ)*zetaCfg ∧
    3*betaA≤markedLocalPathCoefficient r α (t₀/2) p0-(r+4:ℕ)*zetaCfg ∧
    ∃ Kgeom:ℕ,0< Kgeom∧   ∃ kappa0 ξ thetaDeep:ℝ,0< kappa0∧   0<ξ∧   0< thetaDeep∧   ∀ kappa:ℝ,0< kappa →            kappa≤   kappa0 →            
    ∃ ζCut hIcut ε₀ deltaI:ℝ, 0<ζCut ∧ ζCut≤1 ∧ ζCut≤t₀/16 ∧
      0<hIcut ∧ 2*hIcut≤α*p0/4 ∧ 2*hIcut≤t₀/8-ζCut ∧
      0<ε₀ ∧ ε₀≤hIcut ∧ 4*ε₀≤ξ ∧ ε₀≤kappa ∧ ε₀≤α/8 ∧ ε₀≤1/8 ∧
      0<deltaI ∧ deltaI<1/4 ∧ deltaI≤α/32 ∧ deltaI≤p0/32 ∧ 2*deltaI≤t₀/8 ∧
    ∀ ε:ℝ,0<ε → ε≤ε₀ →
    ∃ omegaInner xiDeep:ℝ, 0<omegaInner ∧ omegaInner≤1 ∧ 0<xiDeep ∧
      omegaInner≤ε/8 ∧ omegaInner≤ρ₀*ε/64 ∧ ε^2≤xiDeep ∧ xiDeep≤ξ ∧
      (4*(Kgeom:ℝ)+(3*r+50:ℕ))*xiDeep≤kappa/2 ∧
      (∀ rho t:ℝ,ρ₀≤rho → t₀≤t → (1+2/rho)*xiDeep≤t*omegaInner/32) ∧
    ∀ alphaInner:ℝ,0<alphaInner →
    ∃ betaExt epsilonExt betaRec zetaCommon:ℝ,0< betaExt ∧ 0<epsilonExt ∧ 0<betaRec ∧ 0<zetaCommon ∧ zetaCommon≤kappa/4 ∧
    betaRec≤betaExt ∧ betaRec≤betaA ∧ betaRec≤t₀/4 ∧
    3*betaRec≤markedLocalCycleCoefficient r α (t₀/2) p0-(r+5:ℕ)*zetaCfg ∧
    3*betaRec≤markedLocalPathCoefficient r α (t₀/2) p0-(r+4:ℕ)*zetaCfg ∧
    ∃ gammaMax:ℝ,0<gammaMax ∧ ∀ ζRob:ℝ,0<ζRob → ∀ gammaCap:ℝ,0<gammaCap →
    ∃ gammaStep:ℝ,0<gammaStep ∧ gammaStep≤gammaMax ∧ gammaStep≤gammaCap ∧ ∀ iota aLo B:ℝ,0< iota → 0<aLo → 0≤B →        
    ∃ η ηEnd ζ ζD pmax:ℝ,0<η∧   0<ηEnd∧   0<ζ∧   0<ζD∧   0< pmax∧   pmax≤   1/8∧   
    ∀ (p:ℝ),0<p → p≤1 → p≤pmax →            ∃ θ:ℝ,0<θ∧   
    ∃ delta:ℝ,0< delta∧   ∀ x:ℝ,0< x →    x≤   delta →    
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
    ∀ omegaI:ℝ,0<omegaI →
    ∃ etaBal:ℝ,0<etaBal ∧ ∃ NI:ℕ,
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
    FirstVortexActualParentAlignedProperty r ρ₀ (1/100) t₀ BA δparent zetaCfg kappa x thetaDeep η ε etaBal epsBal ζBal betaA
      (markedLocalCycleCoefficient r α (t₀/2) p0) (markedLocalPathCoefficient r α (t₀/2) p0) ∧
    ∀ d:ℕ,1≤d → ∃ N:ℕ,1≤N ∧
    ∀ rho omega t:ℝ,ρ₀≤rho → rho≤1 → omega₀≤omega → omega≤1 → t₀≤t → (r+4:ℝ)*t≤1 →
    pA0≤rho*(r+4:ℝ)*t/2 → p0≤rho*(r+4:ℝ)*t/2 → p0≤rho*t/2 → p0≤t →
    ∀ (Gamma Color : Type) [Fintype Gamma] [Fintype Color],
    ∀ level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota betaRec aLo B η x omegaI hIcut deltaI etaBal,
      MarkedReferenceLevelStepProperty level (gammaLoss+extra) (sigmaLoss+extra) := by
  intro gamma pA0 omega₀
  obtain ⟨c₀,hbase⟩:=first_vortex_uniform_level_step_choice α ρ₀ hα hαCap hρ₀ hρ₀one
  refine ⟨c₀,?_⟩
  intro r hr hrc t₀ p0 betaConfig betaCommon aLoA BA hbConfig hbCommon haA hBA
  obtain ⟨sstar,tstar,kstar,hsEq,htEq,hkEq,hs,hs1,ht,ht1,hts,htcap,hk,hkhalf,hpBound,hDensity⟩:=
    first_vortex_seed_density_hierarchy r ρ₀ hρ₀ hρ₀one
  have htspoke:t₀≤(1/100)/(((r+4):ℕ):ℝ):=by simpa only [t₀,htEq] using htcap
  obtain ⟨zetaCfg,betaA,hzeta,hbetaA,hbetaConfig,hbetaCommon,hcycle,hpath,Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,hbase⟩:=
    hbase r hr hrc betaConfig betaCommon aLoA BA hbConfig hbCommon haA hBA
  refine ⟨zetaCfg,betaA,hzeta,hbetaA,hbetaConfig,hbetaCommon,hcycle,hpath,Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,?_⟩
  intro kappa hkappa hkk
  obtain ⟨ζCut,hIcut,ε₀,deltaI,hCut,hCutCap,hCutSmall,hi,hiprod,hispoke,he₀,hecut,heξ,heκ,heα,he8,hδ,hδsmall,hδα,hδp,hδt,hbase⟩:=hbase kappa hkappa hkk
  refine ⟨ζCut,hIcut,ε₀,deltaI,hCut,hCutCap,hCutSmall,hi,hiprod,hispoke,he₀,hecut,heξ,heκ,heα,he8,hδ,hδsmall,hδα,hδp,hδt,?_⟩
  intro ε he hecap
  obtain ⟨omegaInner,xiDeep,hOmega,hOmega1,hxiDeep,hωv,hωu,hxiLower,hxiUpper,hxiScale,hxiGap,hbase⟩:=hbase ε he hecap
  refine ⟨omegaInner,xiDeep,hOmega,hOmega1,hxiDeep,hωv,hωu,hxiLower,hxiUpper,hxiScale,hxiGap,?_⟩
  intro alphaInner hAlpha
  obtain ⟨betaExt,epsilonExt,betaRec,zetaCommon,hBetaExt,hEpsilonExt,hbetaRec,hcommon,hcommonCap,hbcap,hba,hbt,hbcycle,hbpath,gammaMax,hGammaMax,hbase⟩:=hbase alphaInner hAlpha
  refine ⟨betaExt,epsilonExt,betaRec,zetaCommon,hBetaExt,hEpsilonExt,hbetaRec,hcommon,hcommonCap,hbcap,hba,hbt,hbcycle,hbpath,gammaMax,hGammaMax,?_⟩
  intro ζRob hζRob gammaCap hgammaCap
  obtain ⟨gammaStep,hγstep,hγcap,hγearly,hbase⟩:=hbase ζRob hζRob gammaCap hgammaCap
  refine ⟨gammaStep,hγstep,hγcap,hγearly,?_⟩
  intro iota aLo B hiota haLo hB
  obtain ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,hbase⟩:=hbase iota aLo B hiota haLo hB
  refine ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,delta,hdelta,hbase⟩:=hbase p hp hp1 hpp
  refine ⟨θ,hθ,delta,hdelta,?_⟩
  intro x hx hxdelta pstarLocal Cparent Clocal
  obtain ⟨sigmaMax,hSigmaMax,sigmaStep,gammaLoss,sigmaLoss,extra,ζCorr,hσstep,hσcap,hγloss,hγlossCap,hσloss,hextra,hγeq,hσeq,hζCorr,hζcap,hinc,hhost,hbase⟩:=hbase x hx hxdelta
  refine ⟨sigmaMax,hSigmaMax,sigmaStep,gammaLoss,sigmaLoss,extra,ζCorr,hσstep,hσcap,hγloss,hγlossCap,hσloss,hextra,hγeq,hσeq,hζCorr,hζcap,hinc,hhost,?_⟩
  intro omegaI hoI
  obtain ⟨etaBal,hetaBal,NI,tolRef,ζActive,τParent,tolParent,ζParent,τ,tolLocal,ζLocal,rowErr,ζRow,epsBal,ζBal,
    htol,htolcap,hζ,hζcap,hκref,hxref,hζκ,hτP,hτPcap,htolP,htolPcap,hζP,hζPcap,hκP,hθP,
    hτ,hτcap,htolLocal,htcap,hbaseLocal,hζLocal,hζLocalCap,hlocal,hrow,hrowcap,hζrow,hζrowcap,hrowmargin,
    heb,hecap,hzb,hzbcap,hbalmargin,hxmargin,hwide,ζWide,δparent,hζWide,hζWideCap,hδparent,hδcfg,hδcommon,hδcut,hδκ,hδcycle,hδpath,
    hδref,hδx,hδp,hδtheta,hδlocal,hδwide,hδrow,hδicut,hbase⟩:=hbase omegaI hoI
  have hAligned:=first_vortex_parent_level_tolerance_alignment r δparent zetaCfg kappa x thetaDeep η t₀ ((1/100)/(((r+4):ℕ):ℝ)) Cparent Clocal ε etaBal epsBal ζBal
    hδparent hx hetaBal heb hzb hδcfg htspoke hδref hδx hδp hδtheta hδwide hδrow
  have hActualAligned:=first_vortex_actual_parent_tolerance_alignment r ρ₀ (1/100) t₀ BA δparent zetaCfg kappa x thetaDeep η ε etaBal epsBal ζBal betaA
    (markedLocalCycleCoefficient r α (t₀/2) p0) (markedLocalPathCoefficient r α (t₀/2) p0)
    hρ₀ (by norm_num) (by simpa only [t₀,htEq] using ht) htspoke hBA.le hδparent hx hetaBal he heb hzb hδcfg hcycle hpath
  exact ⟨etaBal,hetaBal,NI,tolRef,ζActive,τParent,tolParent,ζParent,τ,tolLocal,ζLocal,rowErr,ζRow,epsBal,ζBal,
    htol,htolcap,hζ,hζcap,hκref,hxref,hζκ,hτP,hτPcap,htolP,htolPcap,hζP,hζPcap,hκP,hθP,
    hτ,hτcap,htolLocal,htcap,hbaseLocal,hζLocal,hζLocalCap,hlocal,hrow,hrowcap,hζrow,hζrowcap,hrowmargin,
    heb,hecap,hzb,hzbcap,hbalmargin,hxmargin,hwide,ζWide,δparent,hζWide,hζWideCap,hδparent,hδcfg,hδcommon,hδcut,hδκ,hδcycle,hδpath,
    hδref,hδx,hδp,hδtheta,hδlocal,hδwide,hδrow,hδicut,hAligned,hActualAligned,hbase⟩
end Oberwolfach
