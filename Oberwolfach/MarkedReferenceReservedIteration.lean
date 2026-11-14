module

public import Oberwolfach.MarkedReferenceFiniteIteration
public import Oberwolfach.MarkedReferenceTerminalTransfer
public import Oberwolfach.MarkedReservedTerminalAbsorberProperty

@[expose] public section

/-! A reservoir is chosen before the initial deletion state. The actual
constructed reference-level steps are iterated and their terminal typed
remainder is absorbed in the first reference. This theorem still requires
the displayed fixed level inputs and the reserved absorber property. -/
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

theorem marked_reference_reserved_iteration
    (levels:ℕ → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (count:ℕ) (hcount:0<count) (gammaLoss sigmaLoss ε:ℝ) (s a₀ b₀ e₀ f:ℕ):
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
    MarkedReservedTerminalAbsorberProperty tail head ktail khead H₀ HK π (3*d) r s a₀ b₀ e₀ f ε →
    X.card+Y.card≤s →
    ∀ (W₀:Finset VP) (B₀:Finset UP), X⊆W₀ → Y⊆B₀ →
      (W₀.card:ℝ)≤ε*Fintype.card VP+f → (B₀.card:ℝ)≤ε*Fintype.card VP+f →
    ∀ F₀:Finset (Finset VP⊕(VP×UP)),F₀.card≤f →
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π UP,
      Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π W₀ B₀ e) ∧
      HasResourceDecomposition R C.edges ∧
      ∀ D₀:MarkedReferenceDeletion (levels 0).PP π d (levels 0).σBase,
        D₀.Valid (levels 0).HBase (r+4) (levels 0).I (levels 0).J
          (gammaLoss*Fintype.card VP) (sigmaLoss*Fintype.card VP) →
        let B:=(D₀.remaining (levels 0).HBase).image (markedResourceEmbedding (chain.intoV 0).toEmbedding (chain.intoU 0));
        Disjoint C.edges B → HasResourceDecomposition R (C.edges∪B) := by
  intro chain hsteps VP UP E K tail head ktail khead H₀ HK π R last X Y habs hs W₀ B₀ hXW hYB hW hB F₀ hF
  letI : ∀ i,Fintype (levels i).VP := fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP := fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP := fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP := fun i=>(levels i).inst10
  let A₀:=Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)
  let S₀:=Finset.univ.filter (fun z:VP×UP=>(H₀ z.1 z.2∨HK z.1 z.2)∧z.1∈X∧z.2∈Y)
  have hrows:markedRemainderRows tail head ktail khead A₀ S₀⊆X:=by
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · rcases Finset.mem_union.mp hv with hv|hv
      · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp ha).2.1
      · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp ha).2.2
    · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hz).2.2.1
  have hhubs:markedRemainderHubs S₀⊆Y:=by
    intro u hu
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hu
    exact (Finset.mem_filter.mp hz).2.2.2
  have hsp:∀ z∈S₀,H₀ z.1 z.2∨HK z.1 z.2:=fun z hz=>(Finset.mem_filter.mp hz).2.1
  obtain ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,hCabs⟩:=habs X Y hs W₀ B₀ hXW hYB hW hB F₀ hF A₀ S₀ hrows hhubs hsp
  refine ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,?_⟩
  intro D₀ hD₀ B hCB
  obtain ⟨L,hLB,hdec,hInner,hRep⟩:=marked_reference_finite_iteration levels count hcount gammaLoss sigmaLoss chain hsteps D₀ hD₀
  have hlast:last<count := by dsimp only [last];omega
  have hglobal:=marked_reference_terminal_transfer levels chain last hlast L hRep
  unfold MarkedAmbientTerminalRepresentation at hglobal
  dsimp only at hglobal
  obtain ⟨A,S,hS,hA,hSY,hdiv,hL⟩:=hglobal
  have hAA:A⊆A₀:=by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hA a ha⟩
  have hSS:S⊆S₀:=by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp (hS hz)).2,(hSY z hz).1,(hSY z hz).2⟩
  have hAbs:=hCabs A hAA S hSS hdiv
  have hAbsDec:HasResourceDecomposition R (C.edges∪L):=by
    rw [hL]
    exact hAbs.2.2
  have hdis:Disjoint (B\L) (C.edges∪L):=by
    apply Finset.disjoint_union_right.mpr
    exact ⟨hCB.symm.mono_left Finset.sdiff_subset,
      Finset.disjoint_left.mpr (fun _ he hf=>(Finset.mem_sdiff.mp he).2 hf)⟩
  have hwhole:=resource_decomposition_union R _ _ hdec hAbsDec hdis
  have heq:(B\L)∪(C.edges∪L)=C.edges∪B:=by
    ext e
    have hh:=fun he=>hLB (x:=e) he
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  rwa [heq] at hwhole

end Oberwolfach
