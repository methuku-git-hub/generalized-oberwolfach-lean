module

public import Oberwolfach.FirstVortexUniformLevelActualParentTailExactMargin

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexLevelAfterVortexExactMargin
    (r Kgeom:ℕ) (α ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε:ℝ):Prop :=
    let gamma:=α/16
    let pA0:=ρ₀/400
    let omega₀:=ρ₀/8
    let t₀:=1/(200*((r+4:ℕ):ℝ))
    let p0:=ρ₀/(800*((r+4:ℕ):ℝ));
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
      MarkedReferenceLevelStepProperty level (gammaLoss+extra) (sigmaLoss+extra)
end Oberwolfach
