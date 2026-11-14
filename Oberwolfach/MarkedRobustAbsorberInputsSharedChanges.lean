module

public import Oberwolfach.CommonWitnessSharedChanges
public import Oberwolfach.CommonWitnessMargins
public import Oberwolfach.MarkedHostCountsSharedChanges
public import Oberwolfach.MarkedProfileMonotonicity

@[expose] public section
/-! The same corrected host simultaneously inherits every fixed-weight
common-hub witness and the extension counts needed for robust absorption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_robust_absorber_inputs_after_shared_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (hr:1≤r) (hn:0<Fintype.card V)
    (D τweight A B p k s₀ pstar:ℝ) (hB:0≤B)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀*s₀/((r+4:ℕ):ℝ))
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀*s₀/((r+4:ℕ):ℝ)≤1)
    (weight:(Fin (r+4+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τweight A B weight)
    (es eo el bc bp c ch delta es' eo' el' bc' bp' c' ch':ℝ) (hdelta:0≤delta)
    (σ σnew:RawMarkedOutcome V U Γ Color) (H Hnew:Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hchangeR:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d σnew a)→markedPairPhysical π a∈FR.edgeFinset)
    (hchangeS:∀b v z,¬(H b v z↔Hnew b v z)→FS.Adj (Sum.inl v) (Sum.inr z))
    (hrim:∀x,(FR.degree x:ℝ)≤delta) (hspoke:∀z,(FS.degree z:ℝ)≤delta)
    (hes:es+2*delta/Fintype.card V≤es') (heo:eo+4*delta/Fintype.card V≤eo')
    (hel:el+20*((r+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*delta/Fintype.card V≤el')
    (hbc:bc'≤bc-3*(r+5:ℕ)*delta/Fintype.card V)
    (hbp:bp'≤bp-4*(r+5:ℕ)*delta/Fintype.card V)
    (hc:c'≤c-4*delta) (hch:ch'≤ch-(r+11)*delta)
    (hwitness:∀u u':U,u≠u'→∃κ,CommonWitnessEstimates P π d r D p k s₀ es eo el bc bp weight σ H κ u u'):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let E':=MarkedSampleArc P π (3*d) (fun e=>σnew (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σnew (Sum.inl e)) true;
    MarkedHostExtensionCounts (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H false) (H true) π (3*d) r c ch →
    (∀u u':U,u≠u'→∃κ,CommonWitnessEstimates P π d r D p k s₀ es' eo' el' bc' bp' weight σnew Hnew κ u u') ∧
    MarkedHostExtensionCounts (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (Hnew false) (Hnew true) π (3*d) r c' ch':=by
  intro E K E' K' Q
  constructor
  · intro u u' hu
    obtain ⟨κ,hκ⟩:=hwitness u u' hu
    refine ⟨κ,?_⟩
    have hh:=common_witness_after_shared_changes P π d r hr hn D τweight A B p k s₀ pstar hB
      hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 weight hw es eo el bc bp delta hdelta σ σnew H Hnew κ u u' hκ
      FR FS hchangeR hchangeS hrim (fun z=>hspoke (Sum.inr z))
    exact commonWitnessEstimates_mono P π d r D p k s₀ weight σnew Hnew κ u u' hes heo hel hbc hbp hh
  · have hh:=marked_sample_host_extensions_after_shared_changes P π d r σ σnew H Hnew c ch delta hdelta FR FS hrim hspoke hchangeR hchangeS Q
    exact hh.lowerBounds hc hch
end Oberwolfach
