module

public import Oberwolfach.MarkedHostChangeGraphCounts
public import Oberwolfach.MarkedCommonReferenceCompletion
public import Oberwolfach.MarkedCommonTerminalAgreement
public import Oberwolfach.MarkedCommonSubhostAgreement
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

theorem marked_reference_completion_from_change_graphs
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
    ∀ (σ:RawMarkedOutcome V U Gamma Color) (Hold:Bool→V→U→Prop) (ζ:ℝ),
    (∀ x y,x∈I→y∈I→σ (Sum.inl s(x,y))=(levels 0).σBase (Sum.inl s(x,y)))→
    (∀ b v u,v∈I→u∈J→(Hold b v u↔(levels 0).HBase b v u))→
    (∀ v u,¬(Hold false v u∧Hold true v u))→
    ∀ (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    (∀ x y,P.Adj x y→σ (Sum.inl s(x,y))≠(levels 0).σBase (Sum.inl s(x,y))→FR.Adj x y)→
    (∀ b v u,Hold b v u→¬(levels 0).HBase b v u→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀ x,(FR.degree x:ℝ)≤ζ*Fintype.card V)→
    (∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V)→
    (∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V)→
      (∀ z,(DS.degree z:ℝ)≤ζ*Fintype.card V)→
      let σ':=rawMarkedDeleteRims σ DR.edgeFinset
      let H':=markedDeletePhysicalSpokes Hold DS
      let E:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
      let K:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
      MarkedReservedTerminalAbsorberProperty (fun e:E=>e.val.1) (fun e:E=>e.val.2)
        (fun e:K=>e.val.1) (fun e:K=>e.val.2) (H' false) (H' true) π (3*d) r s a₀ b₀ e₀ f ε)→
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
  intro chain hsteps V U P π I J X Y σ Hold ζ hrim hsp htypes FR FS hchangeR hchangeS hdegR hdegS huniform
    hs hI hJ hG hStar E' K' tail' head' ktail' khead' H₀' HK' S Full hdiv
  letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10
  have hcountR:∀ x,((Finset.univ.filter (fun y=>P.Adj x y∧
      σ (Sum.inl s(x,y))≠(levels 0).σBase (Sum.inl s(x,y)))).card:ℝ)≤ζ*Fintype.card V:=by
    intro x
    have hh:(↑((Finset.univ.filter (fun y=>P.Adj x y∧
      σ (Sum.inl s(x,y))≠(levels 0).σBase (Sum.inl s(x,y)))).card):ℝ)≤FR.degree x:=by
      exact_mod_cast marked_rim_host_change_count P FR σ (levels 0).σBase hchangeR x
    exact hh.trans (hdegR x)
  obtain ⟨hrow,hcol⟩:=marked_spoke_host_change_counts FS Hold (levels 0).HBase hchangeS
  have hcountS:∀ v,((Finset.univ.filter (fun u=>∃ b,Hold b v u∧¬(levels 0).HBase b v u)).card:ℝ)≤ζ*Fintype.card V:=by
    intro v
    have hh:(↑((Finset.univ.filter (fun u=>∃ b,Hold b v u∧¬(levels 0).HBase b v u)).card):ℝ)≤FS.degree (Sum.inl v):=by exact_mod_cast hrow v
    exact hh.trans (hdegS (Sum.inl v))
  have hcountU:∀ u,((Finset.univ.filter (fun v=>∃ b,Hold b v u∧¬(levels 0).HBase b v u)).card:ℝ)≤ζ*Fintype.card V:=by
    intro u
    have hh:(↑((Finset.univ.filter (fun v=>∃ b,Hold b v u∧¬(levels 0).HBase b v u)).card):ℝ)≤FS.degree (Sum.inr u):=by exact_mod_cast hcol u
    exact hh.trans (hdegS (Sum.inr u))
  exact marked_reference_completion_after_host_changes levels count hcount gammaLoss sigmaLoss ε s a₀ b₀ e₀ f chain hsteps
    σ Hold ζ hrim hsp htypes hcountR hcountS hcountU huniform hs hI hJ hG hStar hdiv
end Oberwolfach
