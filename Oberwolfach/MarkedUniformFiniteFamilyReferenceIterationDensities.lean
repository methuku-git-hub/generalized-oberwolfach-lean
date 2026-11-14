module

public import Oberwolfach.MarkedUniformReferenceFiniteIterationDensities
public import Oberwolfach.MarkedUniformReferenceFiniteIteration
public import Oberwolfach.MarkedFiniteReferenceChain

@[expose] public section
/-! The actual finite cover-down iteration needs records only on its finite
prefix. No assumption about unused vortex levels is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_uniform_finite_family_reference_iteration_uniform_densities (gamma pA0:ℝ)
    (hg:0< gamma) (hg1:gamma≤   1) (hpA0:0< pA0) (hpA01:pA0≤   1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤r→c₀≤r+5→∀ rho₀ omega₀ t₀ p0 betaA aLoA BA:ℝ,
    0<rho₀ → rho₀≤1 → 0<omega₀ → 0<t₀ → t₀≤1 → 0<p0 → p0≤1/2 → 0<betaA → 0<aLoA → 0<BA →
    ∃ Kgeom:ℕ,0< Kgeom∧   ∃ kappa0 ξ thetaDeep:ℝ,0< kappa0∧   0<ξ∧   0< thetaDeep∧   ∀ kappa:ℝ,0< kappa →            kappa≤   kappa0 →            
    ∀ alphaInner omegaInner:ℝ,0< alphaInner →         0< omegaInner →         omegaInner≤   1 →         
    ∃ betaExt epsilonExt:ℝ,0< betaExt∧   0< epsilonExt∧   
    ∃ gammaMax:ℝ,0<gammaMax ∧ ∀ gammaLoss iota β aLo B:ℝ,0<gammaLoss → gammaLoss≤gammaMax →   0< iota →        0<β →        β≤   betaExt →        0< aLo →        0≤   B →        
    ∃ η ηEnd ζ ζD pmax:ℝ,0<η∧   0<ηEnd∧   0<ζ∧   0<ζD∧   0< pmax∧   pmax≤   1/8∧   
    ∀ (p:ℝ) (hp:0< p) (hp1:p≤   1),p≤   pmax →            ∃ θ:ℝ,0<θ∧   
    ∃ delta:ℝ,0< delta∧   ∀ x:ℝ,0< x →    x≤   delta →    
    ∃ sigmaMax:ℝ,0<sigmaMax ∧ ∀ sigmaLoss:ℝ,0<sigmaLoss → sigmaLoss≤sigmaMax →  ∀ omegaI hIcut deltaI:ℝ,0< omegaI →    0< hIcut →    0< deltaI →    deltaI<1/4 →    
    ∃ etaBal:ℝ,0< etaBal∧   ∃ NI:ℕ,∀ d:ℕ,1≤   d →            ∃ N:ℕ,1≤   N∧   
    ∀ rho omega t:ℝ,rho₀≤rho → rho≤1 → omega₀≤omega → omega≤1 → t₀≤t → (r+4:ℝ)*t≤1 →
    pA0≤rho*(r+4:ℝ)*t/2 → p0≤rho*(r+4:ℝ)*t/2 → p0≤rho*t/2 → p0≤t →
    ∀ (Gamma Color:Type) [Fintype Gamma] [Fintype Color],
    ∀ (count:ℕ) (hc:0<count),
    ∀ R:Fin count → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal,
    letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
    letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
    letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
    letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10;
    ∀ C:MarkedFiniteReferenceChain hc R,
    let levels:=markedFiniteLevels hc R
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    let chain:=markedFiniteReferenceChainToChain hc R C;
    ∀ D₀:MarkedReferenceDeletion (levels 0).PP (levels 0).πP d (levels 0).σBase,
    D₀.Valid (levels 0).HBase (r+4) (levels 0).I (levels 0).J
      (gammaLoss*Fintype.card (levels 0).VP) (sigmaLoss*Fintype.card (levels 0).VP) →
    let E₀:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) false
    let K₀:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) true
    let R₀:=fun W:MarkedWheel (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
      (r+4) (levels 0).πP (3*d) ((levels 0).HBase false) ((levels 0).HBase true)=>markedWheelPhysicalResources W
    let B₀:=(D₀.remaining (levels 0).HBase).image (markedResourceEmbedding (chain.intoV 0).toEmbedding (chain.intoU 0));
    ∃ L:Finset (Finset (levels 0).VP⊕((levels 0).VP×(levels 0).UP)),L⊆B₀ ∧
      HasResourceDecomposition R₀ (B₀\L) ∧
      let last:=count-1
      let E:=MarkedSampleArc (levels last).PP (levels last).πP (3*d) (fun e=>(levels last).σBase (Sum.inl e)) false
      let K:=MarkedSampleArc (levels last).PP (levels last).πP (3*d) (fun e=>(levels last).σBase (Sum.inl e)) true
      let S:=Finset.univ.filter (fun z:(levels last).VP×(levels last).UP=>
        (levels last).HBase false z.1 z.2∨(levels last).HBase true z.1 z.2)
      let Full:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        (levels last).πP Finset.univ S;
      L⊆((Full.filter (markedInnerResource (levels last).I (levels last).J)).image
        (markedResourceEmbedding (chain.intoV last).toEmbedding (chain.intoU last))) ∧
      MarkedReferenceTerminalRepresentation (levels last) (chain.intoV last).toEmbedding (chain.intoU last) L := by
  obtain ⟨c₀,hcover⟩ := marked_uniform_reference_finite_iteration_uniform_densities gamma pA0 hg hg1 hpA0 hpA01
  refine ⟨c₀,?_⟩
  intro r hr hrc rho₀ omega₀ t₀ p0 betaA aLoA BA hrho₀ hrho₀1 ho₀ ht₀ ht₀1 hp0 hp01 hbA haA hBA
  obtain ⟨Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,hcover⟩ :=
    hcover r hr hrc rho₀ omega₀ t₀ p0 betaA aLoA BA hrho₀ hrho₀1 ho₀ ht₀ ht₀1 hp0 hp01 hbA haA hBA
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
  intro rho omega t hρ hrho1 hω ho1 htlo ht1 hPA0 hpr hpk hpt
  intro Gamma Color _ _ count hc R C levels chain
  letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
  letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
  letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
  letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10
  letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10
  exact hcover rho omega t hρ hrho1 hω ho1 htlo ht1 hPA0 hpr hpk hpt Gamma Color levels count hc chain
end Oberwolfach
