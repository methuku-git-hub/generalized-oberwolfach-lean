module

public import Oberwolfach.MarkedProtectedCorrectionAbsorberLateSize
public import Oberwolfach.MarkedProtectedAbsorbableCorrection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem marked_protected_correction_absorbable (r:ℕ) (εAbs ω h δ ζ:ℝ)
    (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4) (hζ:0<ζ):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀(size a₀ b₀ e₀ f₀:ℕ) (η:ℝ),0≤η→η≤η₀→
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
      n₀≤Fintype.card V→ω*Fintype.card V≤Fintype.card U→Fintype.card U≤Fintype.card V→
    ∀(P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
      (H:Bool→V→U→Prop) (T:Finset V) (W:Finset U),
      (∀v u,¬(H false v u∧H true v u))→(∀v,π v∈T↔v∈T)→
      (T.card:ℝ)≤h*Fintype.card V→(W.card:ℝ)≤h*Fintype.card U→
      (∀(DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
        (∀v,(DR.degree v:ℝ)≤ζ*Fintype.card V)→(∀z,(DS.degree z:ℝ)≤ζ*Fintype.card V)→
        let σ':=rawMarkedDeleteRims σ DR.edgeFinset
        let H':=markedDeletePhysicalSpokes H DS
        let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
        let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
        MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
          (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs)→
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
      (∀v,|occurrenceDegree (Sum.elim tail ktail) v-
        (∑u,if H false v u then (1:ℝ) else 0)-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V)→
      (∀v,|occurrenceDegree (Sum.elim head khead) v-
        (∑u,if H false v u then (1:ℝ) else 0)-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V)→
      (∀v,|occurrenceDegree khead v-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V)→
      (∀u,|(∑v,if H false v u then (1:ℝ) else 0)-((r+4):ℝ)*(∑v,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V)→
      BipartiteLargeCut (occurrenceMultiplicity tail head) δ (2*h)→
      BipartiteLargeCut (occurrenceMultiplicity ktail khead) δ (2*h)→
      BipartiteLargeCut (relationMultiplicity (H false)) δ (2*h)→
      BipartiteLargeCut (relationMultiplicity (H true)) δ (2*h)→
    MarkedProtectedAbsorbableCorrection P π d r size a₀ b₀ e₀ f₀ εAbs ζ σ H T W:=by
  obtain ⟨ξ,hξ,η₀,hη₀,N,hN⟩:=marked_protected_canonical_correction_absorber_late_size
    (r+4) r (by omega) rfl εAbs ω h δ ζ hω hh hδ hδsmall hζ
  refine ⟨η₀,hη₀,N,?_⟩
  intro size a₀ b₀ e₀ f₀ η hη hηsmall V U Γ Color _ _ _ _ _ _ hn hωn hun P π d σ H T W hH hT hTsize hWsize hrob E K tail head ktail khead hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK
  have hbw':∀u,|(∑v,if H false v u then (1:ℝ) else 0)-(((r+4):ℕ):ℝ)*(∑v,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V:=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hbw
  obtain ⟨DA,DS,hsub,_,_,_,_,_,havoid,hrim,hspoke,hdiv,habs⟩:=
    hN size a₀ b₀ e₀ f₀ η hη hηsmall V U Γ Color hn hωn hun P π d σ H T W hH hT hTsize hWsize hrob
      hbp hbm hbk hbw' hcut0 hcutK hcutH0 hcutHK
  exact ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs⟩
end Oberwolfach
