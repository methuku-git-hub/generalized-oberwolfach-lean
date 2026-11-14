module

public import Oberwolfach.MarkedReferenceFiniteIteration
public import Oberwolfach.MarkedReferenceTerminalTransfer

@[expose] public section

/-! Iterate with an absorber that was already selected in the level-zero
host. Its absorption guarantee is quantified over every terminal remainder
before the initial deletion and the cover-down choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

theorem marked_reference_iteration_with_fixed_absorber
    (levels:ℕ → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (count:ℕ) (hcount:0<count) (gammaLoss sigmaLoss:ℝ):
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    ∀ chain:MarkedReferenceLevelChain levels count,
    (∀ i,i<count → MarkedReferenceLevelStepProperty (levels i) gammaLoss sigmaLoss) →
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
    (∀ L,MarkedAmbientTerminalRepresentation (levels 0) X Y L → HasResourceDecomposition R (C∪L)) →
    ∀ D₀:MarkedReferenceDeletion (levels 0).PP π d (levels 0).σBase,
      D₀.Valid (levels 0).HBase (r+4) (levels 0).I (levels 0).J
        (gammaLoss*Fintype.card VP) (sigmaLoss*Fintype.card VP) →
    let B:=(D₀.remaining (levels 0).HBase).image (markedResourceEmbedding (chain.intoV 0).toEmbedding (chain.intoU 0));
    Disjoint C B → HasResourceDecomposition R (C∪B) := by
  intro chain hsteps VP UP E K tail head ktail khead H₀ HK π R last X Y C hAbs D₀ hD₀ B hCB
  letI : ∀ i,Fintype (levels i).VP := fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP := fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP := fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP := fun i=>(levels i).inst10
  obtain ⟨L,hLB,hdec,hInner,hRep⟩:=marked_reference_finite_iteration levels count hcount gammaLoss sigmaLoss chain hsteps D₀ hD₀
  have hlast:last<count := by dsimp only [last];omega
  have hglobal:=marked_reference_terminal_transfer levels chain last hlast L hRep
  have hAbsDec:=hAbs L hglobal
  have hdis:Disjoint (B\L) (C∪L):=by
    apply Finset.disjoint_union_right.mpr
    exact ⟨hCB.symm.mono_left Finset.sdiff_subset,
      Finset.disjoint_left.mpr (fun _ he hf=>(Finset.mem_sdiff.mp he).2 hf)⟩
  have hwhole:=resource_decomposition_union R _ _ hdec hAbsDec hdis
  have heq:(B\L)∪(C∪L)=C∪B:=by
    ext e
    have hh:=fun he=>hLB (x:=e) he
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  rwa [heq] at hwhole
end Oberwolfach
