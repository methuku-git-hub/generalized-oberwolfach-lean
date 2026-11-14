module

public import Oberwolfach.MarkedUniformReferenceLevelConstructorDensities
public import Oberwolfach.MarkedUniformReferenceLevelConstructor
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

theorem marked_uniform_reference_level_step_uniform_densities (gamma pA0:ℝ)
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
    ∀ (Gamma Color : Type) [Fintype Gamma] [Fintype Color],
    ∀ level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal,
      MarkedReferenceLevelStepProperty level gammaLoss sigmaLoss := by
  obtain ⟨c₀,hcover⟩ := marked_uniform_reference_level_constructor_uniform_densities gamma pA0 hg hg1 hpA0 hpA01
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
  intro Gamma Color _ _ level
  letI : Fintype level.VP := level.inst7
  letI : Fintype level.UP := level.inst8
  letI : LinearOrder level.VP := level.inst9
  letI : DecidableEq level.UP := level.inst10
  change MarkedReferenceLevelStepProperty level gammaLoss sigmaLoss
  unfold MarkedReferenceLevelStepProperty
  dsimp only
  intro D hD
  obtain ⟨M,hM,hA,hS,hdec,hdiv,hAR,hSR,F,hF,hLF,hEmpty,hInc,hStar,hNext⟩ :=
    hcover rho omega t hρ hrho1 hω ho1 htlo ht1 hPA0 hpr hpk hpt Gamma Color level D hD
  let E:=MarkedSampleArc level.PP level.πP (3*d) (fun e=>level.σBase (Sum.inl e)) false
  let K:=MarkedSampleArc level.PP level.πP (3*d) (fun e=>level.σBase (Sum.inl e)) true
  let S:=Finset.univ.filter (fun z:level.VP×level.UP=>level.HBase false z.1 z.2∨level.HBase true z.1 z.2)
  let L:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
    level.πP (Finset.univ\(D.arcs∪M.biUnion markedWheelArcs)) (S\(D.spokes∪M.biUnion markedWheelSpokePairs))
  have hsub:L⊆D.remaining level.HBase :=
    (marked_reference_state_step_decomposition level.PP level.πP d (r+4) level.σBase level.HBase D M hM hA hS).2.1
  have hInner:L⊆(markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) level.πP Finset.univ S).filter (markedInnerResource level.I level.J) := by
    change L=(markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) level.πP Finset.univ S).filter (markedInnerResource level.I level.J)\F at hLF
    rw [hLF]
    exact Finset.sdiff_subset
  have hRepresentation : ∃ AR:Finset (E⊕K),∃ SR:Finset (level.VP×level.UP), SR⊆S ∧
      (∀ a∈AR,Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1) a∈level.I ∧
        Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2) a∈level.I) ∧
      (∀ z∈SR,z.1∈level.I ∧ z.2∈level.J) ∧
      MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        (level.HBase true) AR SR (r+4) ∧
      L=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2) level.πP AR SR := by
    exact ⟨Finset.univ\(D.arcs∪M.biUnion markedWheelArcs),
      S\(D.spokes∪M.biUnion markedWheelSpokePairs),Finset.sdiff_subset,hAR,hSR,hdiv,rfl⟩
  refine ⟨L,hsub,hInner,hRepresentation,hdec,?_⟩
  intro WNext ZNext _ _ _ _ fNext gNext πNext hcomm hI hJ XNext YNext hX hY
  obtain ⟨Next,hValid,hRemove,hRemain⟩:=hNext WNext ZNext fNext gNext πNext hcomm hI hJ XNext YNext hX hY
  exact ⟨Next,hValid,hRemain⟩

end Oberwolfach
