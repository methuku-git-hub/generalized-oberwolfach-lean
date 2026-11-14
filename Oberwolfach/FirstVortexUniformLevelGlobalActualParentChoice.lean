module

public import Oberwolfach.FirstVortexUniformLevelActualParentChoice
public import Oberwolfach.FirstVortexUniformLevelSelectorAlignedChoice
public import Oberwolfach.FirstVortexUniformLevelAlignedParentChoice
public import Oberwolfach.FirstVortexParentExactGlobalCallerHierarchy

@[expose] public section
/-! The uniform level theorem and exact global caller budgets are chosen in
one hierarchy, with the parent/stability cap fixed before the vortex scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_uniform_level_global_actual_parent_choice
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
    ∃ Kgeom:ℕ,0< Kgeom∧   ∃ kappa0 ξ thetaDeep:ℝ,0< kappa0∧   0<ξ∧   0< thetaDeep∧   ∀ (kappa:ℝ) (hkappa:0<kappa), kappa≤kappa0 →            
    ∃ ζCut hIcut ε₀ deltaI:ℝ, 0<ζCut ∧ ζCut≤1 ∧ ζCut≤t₀/16 ∧
      0<hIcut ∧ 2*hIcut≤α*p0/4 ∧ 2*hIcut≤t₀/8-ζCut ∧
      0<ε₀ ∧ ε₀≤hIcut ∧ 4*ε₀≤ξ ∧ ε₀≤kappa ∧ ε₀≤α/8 ∧ ε₀≤1/8 ∧
      0<deltaI ∧ deltaI<1/4 ∧ deltaI≤α/32 ∧ deltaI≤p0/32 ∧ 2*deltaI≤t₀/8 ∧
    ∀ (hzetaCfg:0<zetaCfg) (hθDeep:0<thetaDeep) (hBA0:0≤BA)
      (stableCap βfinal:ℝ),0<stableCap→0<βfinal→
    let exactCap:=Classical.choose (marked_vortex_fixed_margin_local_correction_cap r kappa (2*α) (ρ₀/4) p0 p0 t₀ p0 zetaCfg thetaDeep (1:ℝ)
      BA p0 (1:ℝ) (1:ℝ) (1:ℝ) hkappa (by positivity) (by positivity) (by dsimp [p0];positivity) (by dsimp [p0];positivity)
      (by dsimp [t₀];positivity) hzetaCfg hθDeep (by norm_num) hBA0 (by dsimp [p0];positivity) (by norm_num) (by norm_num) (by norm_num));
    ∃ cap:ℝ,0<cap ∧ cap≤exactCap ∧ cap≤stableCap ∧ FirstVortexGlobalThenLocalCallerData r ρ₀ cap βfinal ∧
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
    FirstVortexActualParentAlignedRates r ρ₀ (1/100) t₀ BA δparent zetaCfg kappa x thetaDeep η ε etaBal epsBal ζBal betaA
      (markedLocalCycleCoefficient r α (t₀/2) p0) (markedLocalPathCoefficient r α (t₀/2) p0) ∧
    ∀ d:ℕ,1≤d → ∃ N:ℕ,1≤N ∧
    ∀ rho omega t:ℝ,ρ₀≤rho → rho≤1 → omega₀≤omega → omega≤1 → t₀≤t → (r+4:ℝ)*t≤1 →
    pA0≤rho*(r+4:ℝ)*t/2 → p0≤rho*(r+4:ℝ)*t/2 → p0≤rho*t/2 → p0≤t →
    ∀ (Gamma Color : Type) [Fintype Gamma] [Fintype Color],
    ∀ level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota betaRec aLo B η x omegaI hIcut deltaI etaBal,
      MarkedReferenceLevelStepProperty level (gammaLoss+extra) (sigmaLoss+extra) :=by
  intro gamma pA0 omega₀
  obtain ⟨c₀,hbase⟩:=first_vortex_uniform_level_actual_parent_choice α ρ₀ hα hαCap hρ₀ hρ₀one
  refine ⟨c₀,?_⟩
  intro r hr hrc t₀ p0 betaConfig betaCommon aLoA BA hbConfig hbCommon haA hBA
  obtain ⟨zetaCfg,betaA,hzeta,hbetaA,hbetaConfig,hbetaCommon,hcycle,hpath,Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,hbase⟩:=
    hbase r hr hrc betaConfig betaCommon aLoA BA hbConfig hbCommon haA hBA
  refine ⟨zetaCfg,betaA,hzeta,hbetaA,hbetaConfig,hbetaCommon,hcycle,hpath,Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,?_⟩
  intro kappa hkappa hkk
  obtain ⟨ζCut,hIcut,ε₀,deltaI,hCut,hCutCap,hCutSmall,hi,hiprod,hispoke,he₀,hecut,heξ,heκ,heα,he8,hδ,hδsmall,hδα,hδp,hδt,hbase⟩:=hbase kappa hkappa hkk
  refine ⟨ζCut,hIcut,ε₀,deltaI,hCut,hCutCap,hCutSmall,hi,hiprod,hispoke,he₀,hecut,heξ,heκ,heα,he8,hδ,hδsmall,hδα,hδp,hδt,?_⟩
  intro hzetaCfg hθDeep hBA0 stableCap βfinal hstable hβ exactCap
  obtain ⟨cap,hcap,hcapExact,hcapStable,hGlobal⟩:=
    first_vortex_parent_exact_global_caller_hierarchy r kappa (2*α) ρ₀ p0 p0 t₀ p0 zetaCfg thetaDeep BA p0 stableCap βfinal
      hkappa (by positivity) hρ₀ hρ₀one (by dsimp [p0];positivity) (by dsimp [p0];positivity)
      (by dsimp [t₀];positivity) hzetaCfg hθDeep hBA0 (by dsimp [p0];positivity) hstable hβ
  exact ⟨cap,hcap,hcapExact,hcapStable,hGlobal,hbase⟩
end Oberwolfach
