module

public import Oberwolfach.MarkedUniformReferenceLevelStep
public import Oberwolfach.MarkedReferenceReservedCompletion
public import Oberwolfach.MarkedReferenceLevelStepProperty
public import Oberwolfach.MarkedReferenceStateStepDecomposition
public import Oberwolfach.MarkedReferenceDeletionState
public import Oberwolfach.MarkedNextSampleCanonicalRemainder
public import Oberwolfach.MarkedDeletedCoverFixedRemainder
public import Oberwolfach.MarkedReferenceInputStability
public import Oberwolfach.MarkedGlobalCoverInputMargins
public import Oberwolfach.MarkedLocalCoverInputMargins
public import Oberwolfach.MarkedNestedIterationBalanceInputs
public import Oberwolfach.MarkedResourceDomainMonotonicity
public import Oberwolfach.MarkedIterationNeighbourhoodFromResources
public import Oberwolfach.MarkedIterationToleranceChoices

@[expose] public section

/-! Apply protected cover-down to the actual finite deletion of a fixed
reference. All analytic estimates of the current sample are derived from
those of the reference and the displayed global and star allowances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_uniform_reference_reserved_completion (gamma pA0:ℝ)
    (hg:0< gamma) (hg1:gamma≤   1) (hpA0:0< pA0) (hpA01:pA0≤   1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤   r →            c₀≤   r+5 →            ∀ rho omega t p0 betaA aLoA BA:ℝ,
    0< rho →            rho≤   1 →            0< omega →            omega≤   1 →            0< t →            (r+4:ℝ)*t≤   1 →            
    pA0≤   rho*(r+4:ℝ)*t/2 →            0< p0 →            p0≤   rho*(r+4:ℝ)*t/2 →            p0≤   rho*t/2 →            p0≤   t →            0< betaA →            0< aLoA →            0< BA →            
    ∃ Kgeom:ℕ,0< Kgeom∧   ∃ kappa0 ξ thetaDeep:ℝ,0< kappa0∧   0<ξ∧   0< thetaDeep∧   ∀ kappa:ℝ,0< kappa →            kappa≤   kappa0 →            
    ∀ alphaInner omegaInner:ℝ,0< alphaInner →         0< omegaInner →         omegaInner≤   1 →         
    ∃ betaExt epsilonExt:ℝ,0< betaExt∧   0< epsilonExt∧   
    ∃ gammaMax:ℝ,0<gammaMax ∧ ∀ gammaLoss iota β aLo B:ℝ,0<gammaLoss → gammaLoss≤gammaMax →   0< iota →        0<β →        β≤   betaExt →        0< aLo →        0≤   B →        
    ∃ η ηEnd ζ ζD pmax:ℝ,0<η∧   0<ηEnd∧   0<ζ∧   0<ζD∧   0< pmax∧   pmax≤   1/8∧   
    ∀ (p:ℝ) (hp:0< p) (hp1:p≤   1),p≤   pmax →            ∃ θ:ℝ,0<θ∧   
    ∃ delta:ℝ,0< delta∧   ∀ x:ℝ,0< x →    x≤   delta →    
    ∃ sigmaMax:ℝ,0<sigmaMax ∧ ∀ sigmaLoss:ℝ,0<sigmaLoss → sigmaLoss≤sigmaMax →  ∀ omegaI hIcut deltaI:ℝ,0< omegaI →    0< hIcut →    0< deltaI →    deltaI<1/4 →    
    ∃ etaBal:ℝ,0< etaBal∧   ∃ NI:ℕ,∀ d:ℕ,1≤   d →            ∃ N:ℕ,1≤   N∧   
    ∀ (Gamma Color:Type) [Fintype Gamma] [Fintype Color],
    ∀ (levels:ℕ → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
,
    ∀ (count:ℕ), 0<count → ∀ (ε:ℝ) (s a₀ b₀ e₀ f:ℕ),
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    ∀ chain:MarkedReferenceLevelChain levels count,
    let VP:=(levels 0).VP
    let UP:=(levels 0).UP
    let E:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) false
    let K:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let H₀:=(levels 0).HBase false
    let HK:=(levels 0).HBase true
    let π:=(levels 0).πP
    let R:=fun W:MarkedWheel tail head ktail khead (r+4) π (3*d) H₀ HK=>markedWheelPhysicalResources W
    let S:=Finset.univ.filter (fun z:VP×UP=>H₀ z.1 z.2∨HK z.1 z.2)
    let Full:=markedFiniteResources tail head ktail khead π Finset.univ S
    let last:=count-1
    let X:=(levels last).I.image (chain.intoV last)
    let Y:=(levels last).J.image (chain.intoU last);
    MarkedReservedTerminalAbsorberProperty tail head ktail khead H₀ HK π (3*d) r s a₀ b₀ e₀ f ε →
    MarkedRemainderDivisible tail head ktail khead HK Finset.univ S (r+4) →
    X.card+Y.card≤s →
    ((levels 0).I.card:ℝ)≤ε*Fintype.card VP+f →
    ((levels 0).J.card:ℝ)≤ε*Fintype.card VP+f →
    (e₀:ℝ)≤gammaLoss*Fintype.card VP → (e₀:ℝ)≤sigmaLoss*Fintype.card VP →
    ∀ F₀:Finset (Finset VP⊕(VP×UP)),F₀.card≤f →
    HasResourceDecomposition R Full := by
  obtain ⟨c₀,hcover⟩ := marked_uniform_reference_level_step gamma pA0 hg hg1 hpA0 hpA01
  refine ⟨c₀,?_⟩
  intro r hr hrc rho omega t p0 betaA aLoA BA hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  obtain ⟨Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,hcover⟩ :=
    hcover r hr hrc rho omega t p0 betaA aLoA BA hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  refine ⟨Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,?_⟩
  intro kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  obtain ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,hcover⟩ := hcover kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  obtain ⟨gammaMax,hGammaMax,hcover⟩ := hcover
  refine ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,gammaMax,hGammaMax,?_⟩
  intro gammaLoss iota β aLo B hGammaLoss hGammaBound hIota hβ hBetaSmall haLo hB
  obtain ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,hcover⟩ :=
    hcover gammaLoss iota β aLo B hGammaLoss hGammaBound hIota hβ hBetaSmall haLo hB
  refine ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,delta,hdelta,hcover⟩ := hcover p hp hp1 hpp
  refine ⟨θ,hθ,delta,hdelta,?_⟩
  intro x hx hxdelta
  obtain ⟨sigmaMax,hSigmaMax,hcover⟩ := hcover x hx hxdelta
  refine ⟨sigmaMax,hSigmaMax,?_⟩
  intro sigmaLoss hSigmaLoss hSigmaBound omegaI hIcut deltaI hoI hhI hdI hdIs
  obtain ⟨etaBal,hetaBal,NI,hcover⟩ := hcover sigmaLoss hSigmaLoss hSigmaBound omegaI hIcut deltaI hoI hhI hdI hdIs
  refine ⟨etaBal,hetaBal,NI,?_⟩
  intro d hd
  obtain ⟨NN,hNN,hcover⟩ := hcover d hd
  refine ⟨NN,hNN,?_⟩
  intro Gamma Color _ _ levels count hcount ε s a₀ b₀ e₀ f chain
  exact marked_reference_reserved_completion levels count hcount gammaLoss sigmaLoss ε s a₀ b₀ e₀ f chain
    (fun i _=>hcover Gamma Color (levels i))

end Oberwolfach
