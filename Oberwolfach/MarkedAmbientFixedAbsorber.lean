module

public import Oberwolfach.MarkedAmbientTerminalRepresentation
public import Oberwolfach.MarkedFixedAbsorberReferenceIteration

@[expose] public section

/-! An absorber of every typed divisible terminal remainder is an absorber
of every ambient terminal representation used by the finite iteration. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

theorem marked_ambient_terminal_representation_absorbed
    (level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal):
    letI : Fintype level.VP:=level.inst7
    letI : Fintype level.UP:=level.inst8
    letI : LinearOrder level.VP:=level.inst9
    letI : DecidableEq level.UP:=level.inst10
    let V:=level.VP
    let U:=level.UP
    let E:=MarkedSampleArc level.PP level.πP (3*d) (fun e=>level.σBase (Sum.inl e)) false
    let K:=MarkedSampleArc level.PP level.πP (3*d) (fun e=>level.σBase (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let H₀:=level.HBase false
    let HK:=level.HBase true
    let R:=fun Q:MarkedWheel tail head ktail khead (r+4) level.πP (3*d) H₀ HK=>markedWheelPhysicalResources Q;
    ∀ (X:Finset V) (Y:Finset U) (C:Finset (Finset V⊕(V×U))),
    (∀ (A:Finset (E⊕K)) (S:Finset (V×U)),
      (∀ a∈A,Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)→
      (∀ z∈S,z.1∈X∧z.2∈Y∧(H₀ z.1 z.2∨HK z.1 z.2))→
      MarkedRemainderDivisible tail head ktail khead HK A S (r+4)→
      IsResourceAbsorber R (markedFiniteResources tail head ktail khead level.πP A S) C)→
    ∀ L,MarkedAmbientTerminalRepresentation level X Y L→HasResourceDecomposition R (C∪L):=by
  intro V U E K tail head ktail khead H₀ HK R X Y C hAbs L hRep
  unfold MarkedAmbientTerminalRepresentation at hRep
  dsimp only at hRep
  obtain ⟨A,S,hS,hA,hSY,hdiv,hL⟩:=hRep
  have hS':∀ z∈S,z.1∈X∧z.2∈Y∧(H₀ z.1 z.2∨HK z.1 z.2):=by
    intro z hz
    exact ⟨(hSY z hz).1,(hSY z hz).2,(Finset.mem_filter.mp (hS hz)).2⟩
  have ha:=hAbs A S hA hS' hdiv
  rw [hL]
  exact ha.2.2
theorem marked_reference_iteration_with_typed_fixed_absorber
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
  intro chain hsteps VP UP E K tail head ktail khead H₀ HK π R last X Y C hAbs D₀ hD₀ B hCB
  apply marked_reference_iteration_with_fixed_absorber levels count hcount gammaLoss sigmaLoss chain hsteps C
    (marked_ambient_terminal_representation_absorbed (levels 0) X Y C hAbs) D₀ hD₀ hCB
end Oberwolfach
