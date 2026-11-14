module

public import Oberwolfach.MarkedProtectedInnerCorrection
public import Oberwolfach.MarkedSparseCorrectionCanonicalDivisible

@[expose] public section
/-! The protected sparse correction yields a canonical physically deleted
sample with exact marked divisibility, preserving the same inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_protected_canonical_sample_correction (q:ℕ) (hq:1≤q) (ω h δ ξ:ℝ)
    (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4) (hξ:0<ξ)
    (hξh:((q:ℝ)+1)*ξ≤h/100):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀η:ℝ,0≤η→η≤η₀→
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
      n₀≤Fintype.card V→ω*Fintype.card V≤Fintype.card U→Fintype.card U≤Fintype.card V→
    ∀(P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
      (H:Bool→V→U→Prop) (T:Finset V) (W:Finset U),
      (∀v u,¬(H false v u∧H true v u))→(∀v,π v∈T↔v∈T)→
      (T.card:ℝ)≤h*Fintype.card V→(W.card:ℝ)≤h*Fintype.card U→
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
      (∀u,|(∑v,if H false v u then (1:ℝ) else 0)-(q:ℝ)*(∑v,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V)→
      BipartiteLargeCut (occurrenceMultiplicity tail head) δ (2*h)→
      BipartiteLargeCut (occurrenceMultiplicity ktail khead) δ (2*h)→
      BipartiteLargeCut (relationMultiplicity (H false)) δ (2*h)→
      BipartiteLargeCut (relationMultiplicity (H true)) δ (2*h)→
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∃(DA:Finset (E⊕K)) (DS:Finset (V×U)),DS⊆S ∧
      (∀v,((DA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤
        8*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      (∀v,((DS.filter (fun z=>v=z.1)).card:ℝ)≤4*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      (∀u,((DS.filter (fun z=>u=z.2)).card:ℝ)≤4*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      (DA.card:ℝ)≤8*((q:ℝ)+1)*ξ*(Fintype.card V:ℝ)^2 ∧
      (DS.card:ℝ)≤4*((q:ℝ)+1)*ξ*(Fintype.card V:ℝ)^2 ∧
      (markedFiniteResources tail head ktail khead π DA DS).filter (markedInnerResource T W)=∅ ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ DA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) q:=by
  obtain ⟨η₀,hη₀,N,hN⟩:=marked_protected_inner_correction q hq ω h δ ξ hω hh hδ hδsmall hξ hξh
  refine ⟨η₀,hη₀,N,?_⟩
  intro η hη hηsmall V U Γ Color _ _ _ _ _ _ hn hωn hun P π d σ H T W hH hT hTsize hWsize E K tail head ktail khead hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK S
  have hp:=markedSampleArc_physical_injective P π (3*d) (fun e=>σ (Sum.inl e))
  obtain ⟨hinj,hkinj⟩:=markedPhysicalEdge_endpoint_injections tail head ktail khead π hp
  obtain ⟨DA,DS,hsub,hdeg,hrow,hcol,hcardA,hcardS,hdiv,havoid⟩:=
    hN η hη hηsmall V U E K hn hωn hun tail head ktail khead hinj hkinj
      (H false) (H true) hH π T W hT hTsize hWsize hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK
  refine ⟨DA,DS,hsub,hdeg,hrow,?_,hcardA,hcardS,havoid,?_⟩
  · intro u; simpa only [eq_comm] using hcol u
  · have hdecE:(fun a b:E=>Classical.propDecidable (a=b))=(Subtype.instDecidableEq:DecidableEq E):=Subsingleton.elim _ _
    have hdecK:(fun a b:K=>Classical.propDecidable (a=b))=(Subtype.instDecidableEq:DecidableEq K):=Subsingleton.elim _ _
    try rw [hdecE,hdecK] at hdiv
    exact marked_sparse_correction_canonical_divisible P π d q σ H DA DS hdiv
end Oberwolfach
