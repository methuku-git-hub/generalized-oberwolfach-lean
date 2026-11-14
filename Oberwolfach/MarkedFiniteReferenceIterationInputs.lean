module

public import Oberwolfach.MarkedFiniteReferenceChain

@[expose] public section
/-! Prepare the existing iteration interface from a finite compatible family.
The step hypotheses are not asserted here: they must be proved at the actual
sampled vortex levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

theorem marked_finite_reference_iteration_inputs
    (count:ℕ) (hc:0<count)
    (R:Fin count → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (gammaLoss sigmaLoss:ℝ):
    letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
    letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
    letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
    letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10;
    MarkedFiniteReferenceChain hc R →
    (∀ j:Fin count,MarkedReferenceLevelStepProperty (R j) gammaLoss sigmaLoss) →
    let levels:=markedFiniteLevels hc R
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    Nonempty (MarkedReferenceLevelChain levels count) ∧
    (∀ i,i<count→MarkedReferenceLevelStepProperty (levels i) gammaLoss sigmaLoss) ∧
    (∀ i (hi:i<count),levels i=R ⟨i,hi⟩):=by
  intro C hstep levels
  letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
  letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
  letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
  letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10
  constructor
  · exact ⟨markedFiniteReferenceChainToChain hc R C⟩
  constructor
  · intro i hi
    exact hstep (markedReferenceClip hc i)
  · intro i hi
    exact markedFiniteLevels_prefix hc R hi
end Oberwolfach
