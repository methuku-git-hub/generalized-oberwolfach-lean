module

public import Oberwolfach.MarkedAmbientFixedAbsorber
public import Oberwolfach.MarkedFiniteReferenceIterationInputs

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}
theorem marked_finite_reference_iteration_with_typed_fixed_absorber
    (count:ℕ) (hcount:0<count)
    (levelsFinite:Fin count → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (gammaLoss sigmaLoss:ℝ):
    letI : ∀ i,Fintype (levelsFinite i).VP:=fun i=>(levelsFinite i).inst7
    letI : ∀ i,Fintype (levelsFinite i).UP:=fun i=>(levelsFinite i).inst8
    letI : ∀ i,LinearOrder (levelsFinite i).VP:=fun i=>(levelsFinite i).inst9
    letI : ∀ i,DecidableEq (levelsFinite i).UP:=fun i=>(levelsFinite i).inst10
    let levels:=markedFiniteLevels hcount levelsFinite
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    ∀ finiteChain:MarkedFiniteReferenceChain hcount levelsFinite,
    (∀ i:Fin count,MarkedReferenceLevelStepProperty (levelsFinite i) gammaLoss sigmaLoss) →
    let chain:=markedFiniteReferenceChainToChain hcount levelsFinite finiteChain;
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
    let last:=count-1
    let X:=(levels last).I.image (chain.intoV last)
    let Y:=(levels last).J.image (chain.intoU last);
    ∀ C:Finset (Finset VP⊕(VP×UP)),
    (∀ (A:Finset (E⊕K)) (S:Finset (VP×UP)),
      (∀ a∈A,Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)→
      (∀ z∈S,z.1∈X∧z.2∈Y∧(H₀ z.1 z.2∨HK z.1 z.2))→
      MarkedRemainderDivisible tail head ktail khead HK A S (r+4)→
      IsResourceAbsorber R (markedFiniteResources tail head ktail khead π A S) C) →
    ∀ D₀:MarkedReferenceDeletion (levels 0).PP π d (levels 0).σBase,
      D₀.Valid (levels 0).HBase (r+4) (levels 0).I (levels 0).J
        (gammaLoss*Fintype.card VP) (sigmaLoss*Fintype.card VP) →
    let B:=(D₀.remaining (levels 0).HBase).image (markedResourceEmbedding (chain.intoV 0).toEmbedding (chain.intoU 0));
    Disjoint C B → HasResourceDecomposition R (C∪B) := by
  intro levels finiteChain hsteps chain
  apply marked_reference_iteration_with_typed_fixed_absorber levels count hcount gammaLoss sigmaLoss chain
  intro i hi
  exact hsteps (markedReferenceClip hcount i)
end Oberwolfach
