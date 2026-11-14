module

public import Oberwolfach.MarkedCommonTerminalTypedAgreement
public import Oberwolfach.MarkedReferenceFixedTransferredCompletion
public import Oberwolfach.MarkedReferenceEncodedTerminalAgreement
public import Oberwolfach.MarkedReservedTerminalAbsorberProperty

@[expose] public section
/-! Choose a fixed absorber in a physically deleted common host after the
later host is known, then run the reference iteration in that later host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

theorem marked_common_reference_typed_completion
    (levels:ℕ→MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (count:ℕ) (hcount:0<count) (gammaLoss sigmaLoss ε:ℝ) (s a₀ b₀ e₀ f:ℕ):
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    ∀ chain:MarkedReferenceLevelChain levels count,
    (∀ i,i<count→MarkedReferenceLevelStepProperty (levels i) gammaLoss sigmaLoss)→
    let V:=(levels 0).VP
    let U:=(levels 0).UP
    let P:=(levels 0).PP
    let π:=(levels 0).πP
    let I:=(levels 0).I
    let J:=(levels 0).J
    let X:=(levels (count-1)).I.image (chain.intoV (count-1))
    let Y:=(levels (count-1)).J.image (chain.intoU (count-1));
    ∀ (σ:RawMarkedOutcome V U Gamma Color) (Hold:Bool→V→U→Prop)
      (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
    (∀ mark x y,x∈I→y∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) mark x y=1))→
    (∀ mark x y,x∈I→y∈I→
      markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=
      markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y)→
    (∀ mark x y,markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=1→
      markedPhysicalRim P π (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) mark x y=1)→
    (∀ b v u,markedDeletePhysicalSpokes Hold DS b v u→(levels 0).HBase b v u)→
    (∀ b v u,v∈I→u∈J→(markedDeletePhysicalSpokes Hold DS b v u↔(levels 0).HBase b v u))→
    let E:=MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let H₀:=markedDeletePhysicalSpokes Hold DS false
    let HK:=markedDeletePhysicalSpokes Hold DS true;
    MarkedReservedTerminalAbsorberProperty tail head ktail khead H₀ HK π (3*d) r s a₀ b₀ e₀ f ε→
    X.card+Y.card≤s→(I.card:ℝ)≤ε*Fintype.card V+f→(J.card:ℝ)≤ε*Fintype.card V+f→
    (e₀:ℝ)≤gammaLoss*Fintype.card V→(e₀:ℝ)≤sigmaLoss*Fintype.card V→
    let E':=MarkedSampleArc P π (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) true
    let tail':=fun e:E'=>e.val.1
    let head':=fun e:E'=>e.val.2
    let ktail':=fun e:K'=>e.val.1
    let khead':=fun e:K'=>e.val.2
    let H₀':=(levels 0).HBase false
    let HK':=(levels 0).HBase true
    let S:=Finset.univ.filter (fun z:V×U=>H₀' z.1 z.2∨HK' z.1 z.2)
    let Full:=markedFiniteResources tail' head' ktail' khead' π Finset.univ S;
    MarkedRemainderDivisible tail' head' ktail' khead' HK' Finset.univ S (r+4)→
    HasResourceDecomposition
      (fun W:MarkedWheel tail' head' ktail' khead' (r+4) π (3*d) H₀' HK'=>markedWheelPhysicalResources W) Full :=by
  intro chain hsteps V U P π I J X Y σ Hold DR DS hrim hcommon hsubR hsubS hinnerS E K tail head ktail khead H₀ HK
    habs hs hI hJ hG hStar E' K' tail' head' ktail' khead' H₀' HK' S Full hdiv
  letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10
  obtain ⟨hXI,hYJ⟩:=marked_reference_terminal_pair_in_first_pair levels chain hcount
  let A₀:=Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)
  let S₀:=Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧z.1∈X∧z.2∈Y)
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
  have hsp₀:∀ z∈S₀,H₀ z.1 z.2∨HK z.1 z.2:=fun z hz=>(Finset.mem_filter.mp hz).2.1
  obtain ⟨C,_,hCe,_,_,hCold,hCdec,hCabs⟩:=habs X Y hs I J hXI hYJ hI hJ ∅ (by simp) A₀ S₀ hrows hhubs hsp₀
  have hA:=marked_common_terminal_arc_agreement_typed P π d σ (levels 0).σBase DR I X hXI hrim hcommon
  have hS:=marked_reference_terminal_spoke_agreement levels count hcount chain (markedDeletePhysicalSpokes Hold DS) hinnerS
  have hCE:∀ e:E,Sum.inl ({tail e,head e}:Finset V)∈C.edges→∃ e':E',tail' e'=tail e∧head' e'=head e:=by
    intro e _
    exact ⟨⟨e.val,hsubR false e.val.1 e.val.2 e.property⟩,rfl,rfl⟩
  have hCK:∀ e:K,Sum.inl ({ktail e,π (khead e)}:Finset V)∈C.edges→∃ e':K',ktail' e'=ktail e∧khead' e'=khead e:=by
    intro e _
    exact ⟨⟨e.val,hsubR true e.val.1 e.val.2 e.property⟩,rfl,rfl⟩
  have hCard:(C.edges.card:ℝ)≤(e₀:ℝ):=by exact_mod_cast hCe
  have hCG:(C.edges.card:ℝ)≤gammaLoss*Fintype.card V:=hCard.trans hG
  have hCS:(C.edges.card:ℝ)≤sigmaLoss*Fintype.card V:=hCard.trans hStar
  exact marked_reference_completion_with_fixed_transferred_absorber levels count hcount gammaLoss sigmaLoss chain hsteps
    E K tail head ktail khead H₀ HK A₀ S₀ C.edges
    (markedSampleArc_physical_injective P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)))
    hCabs hA hS hCE hCK (fun v u _=>hsubS false v u) (fun v u _=>hsubS true v u)
    hCdec (by
      intro e he
      have hh:=C.supported e he
      cases e with
      | inl a=>
        obtain ⟨t,ht,_,_⟩:=hh
        exact ⟨t,ht⟩
      | inr a=>trivial) hCold hdiv hCG hCS
end Oberwolfach
