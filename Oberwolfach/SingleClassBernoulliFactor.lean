module

public import Oberwolfach.SupportedBernoulliFactor
public import Oberwolfach.EmbeddedFiniteSets

@[expose] public section

/-! The one-class fresh-factor conclusion on the actual vertex subset.
The altered domain and forbidden graph are universally quantified on one
event, and the order and failure bounds use the original domain size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

theorem single_class_bernoulli_factor (r J:ℕ) (hr:3≤r)
    (S:Tpl→VertexAbsorberTemplate r) (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0≤B):
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
      ∀ (W C:Type) [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C],
      ∀ (T:Finset W),N≤T.card→∀ (R:C→Finset W) (w:C→ℝ),
      (∀ C₀,R C₀⊆T)→(∀ C₀,(R C₀).card=r)→
      (∀ U:Finset W,Fintype.card {C₀:C // R C₀=U}≤J)→
      (∀ C₀,b/(T.card:ℝ)^(r-1)≤w C₀ ∧ w C₀≤B/(T.card:ℝ)^(r-1))→
      (∀ v∈T,|1-hypergraphWeightedDegree R w v|≤η)→
      (∀ X:Finset W,X⊆T→X.card=r→
        α*(T.card:ℝ)^(r*r)≤Fintype.card (LabelledAbsorberFamily R S X))→
      1-1/(T.card:ℝ)^q≤
        (FiniteLaw.pi (fun _:W=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ Y:Finset W,Y⊆T → r ∣ Y.card →
            ((((T∩bernoulliVertexSet σ)\Y).card+(Y\(T∩bernoulliVertexSet σ)).card:ℕ):ℝ)≤ζ*(p*T.card)→
            ∀ F:SimpleGraph W,(∀ v,(F.degree v:ℝ)≤ζ*(p*T.card))→
            ∃ D:Finset C,((∀ x∈D,∀ y∈D,x≠y→Disjoint (R x) (R y)) ∧ D.biUnion R=Y) ∧
              ∀ C₀∈D,∀ x∈R C₀,∀ y∈R C₀,¬F.Adj x y):=by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=supported_bernoulli_graph_avoiding_factor
    (fun _:Unit=>r) r J hr (fun _=>by omega) (by simp) S α b B hα hb hB
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro W C _ _ _ _ T hn R w hsupp hR hJ hw herr habs
  let V:Unit→Type:=fun _=>T
  let e:(Σ i,V i)↪W:=⟨fun v=>v.2.val,by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    cases i;cases j
    exact congrArg (Sigma.mk ()) (Subtype.ext h)⟩
  have heT:Finset.univ.image e=T:=by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨i,x⟩,rfl⟩;exact x.property
    · intro hv;exact ⟨⟨(),⟨v,hv⟩⟩,rfl⟩
  have hnV:Fintype.card (Σ i,V i)=T.card:=by simp only [Fintype.card_sigma,V,Fintype.card_coe];simp
  have hprofile (C₀:C) (i:Unit):
      (Finset.univ.filter (fun v:V i=>e ⟨i,v⟩∈R C₀)).card=r:=by
    rw [←hR C₀]
    apply Finset.card_bij (fun v _=>v.val)
    · intro v hv;exact (Finset.mem_filter.mp hv).2
    · intro v _ w _ h;exact Subtype.ext h
    · intro v hv;exact ⟨⟨v,hsupp C₀ hv⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
  have hevent:=hN V W C (by simpa only [hnV] using hn) e R w
    (fun C₀ v hv=>⟨⟨(),⟨v,hsupp C₀ hv⟩⟩,rfl⟩) hprofile hJ
    (by simpa only [hnV] using hw) (fun v=>herr _ v.2.property) (by
      intro ρ
      let X:=(profileRootSet ρ).image e
      have hXT:X⊆T:=by
        intro v hv;obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp hv;exact z.2.property
      have hXr:X.card=r:=by
        rw [Finset.card_image_of_injective _ e.injective,profileRootSet_card]
        simp
      simpa only [hnV] using habs X hXT hXr)
  rw [hnV] at hevent
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y hYT hdiv hchange F hF
  obtain ⟨k,hk⟩:=hdiv
  let Y':=embeddedPreimage e Y
  have hYsupp:∀ v∈Y,∃ z,e z=v:=fun v hv=>⟨⟨(),⟨v,hYT hv⟩⟩,rfl⟩
  have hYcard:Y'.card=Y.card:=embeddedPreimage_card e Y hYsupp
  have hYprofile (i:Unit):
      (Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y')).card=r*k:=by
    cases i
    have hc:=sigma_finset_card Y'
    simp only [Finset.univ_unique,Finset.sum_singleton] at hc
    exact hc.symm.trans (hYcard.trans hk)
  have hdiff:(((bernoulliVertexSet (fun z=>σ (e z))\Y').card+
      (Y'\bernoulliVertexSet (fun z=>σ (e z))).card:ℕ):ℝ)≤ζ*(p*T.card):=by
    rw [embedded_bernoulli_alteration e σ Y hYsupp,heT]
    exact hchange
  obtain ⟨D,hD,havoid⟩:=hσ Y' k hYprofile hdiff F hF
  refine ⟨D,⟨hD.1,?_⟩,havoid⟩
  exact hD.2.trans (embeddedPreimage_image e Y hYsupp)

end Oberwolfach
