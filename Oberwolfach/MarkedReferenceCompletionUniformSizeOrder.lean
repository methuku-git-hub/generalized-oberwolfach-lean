module

public import Oberwolfach.MarkedReferenceCompletionTypedChangeGraphs

@[expose] public section
/-! Fix an order threshold before the level data and derive the absorber size bounds from the level-size fields. -/
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

theorem marked_reference_completion_uniform_size_order
    (count:ℕ) (hcount:0<count) (gammaLoss sigmaLoss ε:ℝ) (s a₀ b₀ e₀ f:ℕ)
    (hξε:ξ≤ε) (hγ:0<gammaLoss) (hσ:0<sigmaLoss):
    ∃ N₀:ℕ,∀ (levels:ℕ→MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal),
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    N₀≤Fintype.card (levels 0).VP→
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
    ∀ (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    (∀ x y,x≠y→markedRemovedPhysicalRim P π d σ (levels 0).σBase s(x,y)→FR.Adj x y)→
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
    X.card+Y.card≤s→
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
  obtain ⟨Ng,hNg⟩:=exists_nat_gt ((e₀:ℝ)/gammaLoss)
  obtain ⟨Ns,hNs⟩:=exists_nat_gt ((e₀:ℝ)/sigmaLoss)
  refine ⟨max Ng Ns,?_⟩
  intro levels hn chain hsteps V U P π I J X Y σ Hold ζ hrim hsp htypes FR FS hchangeR hchangeS hdegR hdegS huniform hs E' K' tail' head' ktail' khead' H₀' HK' S Full hdiv
  letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10
  have hnG:Ng≤Fintype.card V:=(le_max_left _ _).trans hn
  have hnS:Ns≤Fintype.card V:=(le_max_right _ _).trans hn
  have hI:(I.card:ℝ)≤ε*Fintype.card V+f:=by
    have hh:=mul_le_mul_of_nonneg_right hξε (Nat.cast_nonneg (Fintype.card V))
    have hi: (I.card:ℝ)≤ξ*Fintype.card V:=(levels 0).hIsize
    have hf:0≤(f:ℝ):=by positivity
    linarith
  have hJ:(J.card:ℝ)≤ε*Fintype.card V+f:=by
    have hh:=mul_le_mul_of_nonneg_right hξε (Nat.cast_nonneg (Fintype.card V))
    have hi: (J.card:ℝ)≤ξ*Fintype.card V:=(levels 0).hJsize
    have hf:0≤(f:ℝ):=by positivity
    linarith
  have hG:(e₀:ℝ)≤gammaLoss*Fintype.card V:=by
    have hn':(Ng:ℝ)≤Fintype.card V:=by exact_mod_cast hnG
    have hh:((e₀:ℝ)/gammaLoss)*(gammaLoss)<(Fintype.card V:ℝ)*gammaLoss:=
      mul_lt_mul_of_pos_right (hNg.trans_le hn') hγ
    have he:(e₀:ℝ)/gammaLoss*gammaLoss=e₀:=div_mul_cancel₀ _ (ne_of_gt hγ)
    rw [he] at hh
    linarith
  have hS:(e₀:ℝ)≤sigmaLoss*Fintype.card V:=by
    have hn':(Ns:ℝ)≤Fintype.card V:=by exact_mod_cast hnS
    have hh:((e₀:ℝ)/sigmaLoss)*(sigmaLoss)<(Fintype.card V:ℝ)*sigmaLoss:=
      mul_lt_mul_of_pos_right (hNs.trans_le hn') hσ
    have he:(e₀:ℝ)/sigmaLoss*sigmaLoss=e₀:=div_mul_cancel₀ _ (ne_of_gt hσ)
    rw [he] at hh
    linarith
  exact marked_reference_completion_from_typed_change_graphs levels count hcount gammaLoss sigmaLoss ε s a₀ b₀ e₀ f
    chain hsteps σ Hold ζ hrim hsp htypes FR FS hchangeR hchangeS hdegR hdegS huniform hs hI hJ hG hS hdiv
end Oberwolfach
