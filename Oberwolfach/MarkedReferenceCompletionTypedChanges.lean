module

public import Oberwolfach.MarkedCommonReferenceTypedCompletion
public import Oberwolfach.MarkedRimTypedIntersection
public import Oberwolfach.MarkedSpokeCommonSubhost
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

theorem marked_reference_completion_after_typed_host_changes
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
    (∀ mark x y,x∈I→y∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) mark x y=1))→
    (∀ b v u,v∈I→u∈J→(Hold b v u↔(levels 0).HBase b v u))→
    (∀ v u,¬(Hold false v u∧Hold true v u))→
    (∀ x,((Finset.univ.filter (fun y=>x≠y ∧
      markedRemovedPhysicalRim P π d σ (levels 0).σBase s(x,y))).card:ℝ)≤ζ*Fintype.card V)→
    (∀ v,((Finset.univ.filter (fun u=>∃ b,Hold b v u∧¬(levels 0).HBase b v u)).card:ℝ)≤ζ*Fintype.card V)→
    (∀ u,((Finset.univ.filter (fun v=>∃ b,Hold b v u∧¬(levels 0).HBase b v u)).card:ℝ)≤ζ*Fintype.card V)→
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
  intro chain hsteps V U P π I J X Y σ Hold ζ hrim hsp htypes hcountR hcountS hcountU huniform
    hs hI hJ hG hStar E' K' tail' head' ktail' khead' H₀' HK' S Full hdiv
  letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10
  obtain ⟨DR,hP,hdegR,hinterR⟩:=marked_rim_typed_intersection_deletion P π d σ (levels 0).σBase
  obtain ⟨DS,hinterS,_,hdegS,hdegU⟩:=marked_spoke_common_subhost_deletion Hold (levels 0).HBase I J htypes hsp
  have hcommon:∀ mark x y,x∈I→y∈I→
      markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=
      markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y:=by
    intro mark x y hx hy
    have hh:=hinterR mark x y
    have ha:=hrim mark x y hx hy
    have hb:(markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=1 ↔
      markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1):=by
      rw [hh]
      exact ⟨And.left,fun h=>⟨h,ha.mp h⟩⟩
    rw [←markedPhysicalRim_indicator P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y,
      ←markedPhysicalRim_indicator P π (3*d) (fun e=>σ (Sum.inl e)) mark x y]
    exact ite_congr (propext hb) (by intro _;rfl) (by intro _;rfl)
  have hR:∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V:=by
    intro x
    rw [hdegR x]
    exact hcountR x
  have hS:∀ v,(DS.degree (Sum.inl v):ℝ)≤ζ*Fintype.card V:=by
    intro v
    rw [hdegS v]
    exact hcountS v
  have hU:∀ u,(DS.degree (Sum.inr u):ℝ)≤ζ*Fintype.card V:=by
    intro u
    rw [hdegU u]
    exact hcountU u
  have hDS:∀ z,(DS.degree z:ℝ)≤ζ*Fintype.card V:=by
    intro z
    cases z with
    | inl v=>exact hS v
    | inr u=>exact hU u
  have habs:=huniform DR DS hR hDS
  apply marked_common_reference_typed_completion levels count hcount gammaLoss sigmaLoss ε s a₀ b₀ e₀ f chain hsteps σ Hold DR DS
    hrim hcommon (fun mark x y h=>(hinterR mark x y).mp h |>.2)
    (fun b v u h=>(hinterS b v u).mp h |>.2)
    (by intro b v u hv hu;rw [hinterS b v u,hsp b v u hv hu];simp)
    habs hs hI hJ hG hStar hdiv
end Oberwolfach
