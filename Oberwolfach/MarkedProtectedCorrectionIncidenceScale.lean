module

public import Oberwolfach.MarkedReservedTerminalAbsorberProperty
public import Oberwolfach.MarkedCorrectionRobustnessScale
public import Oberwolfach.MarkedCorrectionPhysicalGraphDegrees
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

theorem marked_protected_canonical_correction_absorber_with_scale (q r:ℕ) (hq:1≤q) (hqeq:q=r+4) (εAbs ω h δ ζ:ℝ)
    (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4) (hζ:0<ζ):
    ∃ξ:ℝ,0<ξ ∧ 16*((q:ℝ)+1)*ξ≤ζ ∧ ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀(size a₀ b₀ e₀ f₀:ℕ) (η:ℝ),0≤η→η≤η₀→
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
      (∀v,((markedSampleArcSetGraph P π d σ DA).degree v:ℝ)≤ζ*Fintype.card V) ∧
      (∀z,((markedFiniteSpokeGraph DS).degree z:ℝ)≤ζ*Fintype.card V) ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ DA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) q ∧
    MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs:=by
  obtain ⟨ξ,hξ,hξh,hξrim,hξspoke⟩:=marked_correction_robustness_scale q h ζ hh hζ
  obtain ⟨η₀,hη₀,N,hN⟩:=marked_protected_inner_correction q hq ω h δ ξ hω hh hδ hδsmall hξ hξh
  refine ⟨ξ,hξ,hξrim,η₀,hη₀,N,?_⟩
  intro size a₀ b₀ e₀ f₀ η hη hηsmall V U Γ Color _ _ _ _ _ _ hn hωn hun P π d σ H T W hH hT hTsize hWsize hrob E K tail head ktail khead hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK S
  have hp:=markedSampleArc_physical_injective P π (3*d) (fun e=>σ (Sum.inl e))
  obtain ⟨hinj,hkinj⟩:=markedPhysicalEdge_endpoint_injections tail head ktail khead π hp
  obtain ⟨DA,DS,hsub,hdeg,hrow,hcol,hcardA,hcardS,hdiv,havoid⟩:=
    hN η hη hηsmall V U E K hn hωn hun tail head ktail khead hinj hkinj
      (H false) (H true) hH π T W hT hTsize hWsize hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK
  have hrow':∀v,((DS.filter (fun z=>v=z.1)).card:ℝ)≤8*((q:ℝ)+1)*ξ*Fintype.card V:=by
    intro v
    have hh:=hrow v
    have hn:0≤4*((q:ℝ)+1)*ξ*Fintype.card V:=by positivity
    linarith
  have hcol':∀u,((DS.filter (fun z=>u=z.2)).card:ℝ)≤8*((q:ℝ)+1)*ξ*Fintype.card V:=by
    intro u
    have hh:=hcol u
    have hn:0≤4*((q:ℝ)+1)*ξ*Fintype.card V:=by positivity
    have hh':((DS.filter (fun z=>u=z.2)).card:ℝ)≤4*((q:ℝ)+1)*ξ*Fintype.card V:=by simpa only [eq_comm] using hh
    linarith
  have hgraphs:=marked_correction_physical_graph_degrees tail head ktail khead π DA DS
    (8*((q:ℝ)+1)*ξ*Fintype.card V) (by positivity) hdeg hrow' hcol'
  have hrim:∀v,((markedSampleArcSetGraph P π d σ DA).degree v:ℝ)≤16*((q:ℝ)+1)*ξ*Fintype.card V:=by
    intro v
    have hh:=hgraphs.1 v
    dsimp only [markedSampleArcSetGraph] at ⊢
    nlinarith
  have hrimRob:∀v,((markedSampleArcSetGraph P π d σ DA).degree v:ℝ)≤ζ*Fintype.card V:=by
    intro v
    exact (hrim v).trans (by nlinarith [mul_le_mul_of_nonneg_right hξrim (show (0:ℝ)≤Fintype.card V by positivity)])
  have hspokeRob:∀z,((markedFiniteSpokeGraph DS).degree z:ℝ)≤ζ*Fintype.card V:=by
    intro z
    exact (hgraphs.2 z).trans (by nlinarith [mul_le_mul_of_nonneg_right hξspoke (show (0:ℝ)≤Fintype.card V by positivity)])
  refine ⟨DA,DS,hsub,hdeg,hrow,?_,hcardA,hcardS,havoid,hrimRob,hspokeRob,?_⟩
  · intro u; simpa only [eq_comm] using hcol u
  · have hdecE:(fun a b:E=>Classical.propDecidable (a=b))=(Subtype.instDecidableEq:DecidableEq E):=Subsingleton.elim _ _
    have hdecK:(fun a b:K=>Classical.propDecidable (a=b))=(Subtype.instDecidableEq:DecidableEq K):=Subsingleton.elim _ _
    try rw [hdecE,hdecK] at hdiv
    refine ⟨marked_sparse_correction_canonical_divisible P π d q σ H DA DS hdiv,?_⟩
    exact hrob (markedSampleArcSetGraph P π d σ DA) (markedFiniteSpokeGraph DS) hrimRob hspokeRob
end Oberwolfach
