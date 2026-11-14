module

public import Oberwolfach.MixedPositiveActiveMatching
public import Oberwolfach.PhysicalRimResourceResidual

@[expose] public section
/-! Apply the matching theorem to exactly the sufficiently large incident
physical rim sets, without imposing a size condition on the small ones. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_matching_large_incident_rim_coverage (r B:ℕ) (hr:2≤r) (hB:1≤B)
    (K a γ:ℝ) (hK:0<K) (ha:0<a) (hγ:0<γ):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀n:ℕ,n₀≤n →
    ∀ (I V A X U:Type) [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
      [Fintype A] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
      (E:I→Type) [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]
      (R:∀i,E i→Finset V) (w:∀i,E i→ℝ) (σ:V→Bool)
      (target:I→V→ℝ) (τ t:ℝ) (Kᵢ:I→ℝ),
    let W := {v:V // v∈bernoulliVertexSet σ}
    let e : W↪V := Function.Embedding.subtype _
    let C := RestrictedResource (mixedCandidateResources R) e
    let Q := restrictedResourceSet (mixedCandidateResources R) e
    ∀ (g:A→C→ℝ) (φ:W↪Sym2 X⊕(X×U)),
    Fintype.card W≤n^B → Fintype.card A≤n^B → Fintype.card X≤n^B →
    (∀i c,0<w i c → 2≤(R i c).card ∧ (R i c).card≤r) → (∀i c,0≤w i c) →
    (∀v,v∈bernoulliVertexSet σ → ∑i,target i v=1) →
    (∀i v,v∈bernoulliVertexSet σ →
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) v σ-target i v|≤t+τ*target i v) →
    (Fintype.card I:ℝ)*t+τ≤η₀ →
    (∀i u v,u≠v → resourceOmittedPairWeight (R i) (w i) u v≤Kᵢ i/n) →
    (∑i,Kᵢ i)≤K →
    (∀i c,0≤g i c ∧ g i c≤1) →
    (∀i,a*n≤∑c,g i c*mixedCandidateWeight w c.val) →
    ∃M:Finset C,(∀c∈M,0<mixedCandidateWeight w c.val) ∧
      (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
      (∀x,a*n≤(rimIncidentResources φ x).card →
        (((rimIncidentResources φ x\M.biUnion Q).card:ℕ):ℝ)≤γ*(rimIncidentResources φ x).card) ∧
      (∀i,(1-γ)*(∑c,g i c*mixedCandidateWeight w c.val)≤∑c∈M,g i c) ∧
      (∀i,(∑c∈M,g i c)≤(1+γ)*(∑c,g i c*mixedCandidateWeight w c.val)) :=by
  obtain ⟨η,hη,n₀,hmatch⟩:=mixed_sampled_resource_matching_positive_active_targets r B hr hB K a γ hK ha hγ
  refine ⟨η,hη,n₀,?_⟩
  intro n hn I V A X U _ _ _ _ _ _ _ _ _ E _ _ R w σ target τ t Kᵢ W e C Q g φ hW hA hX hsize hw htarget hload herror hpair hsum hg hmass
  let J:Type:={x:X // a*n≤(rimIncidentResources φ x).card}
  let S:J→Finset W:=fun x=>rimIncidentResources φ x.val
  have hJ:Fintype.card J≤n^B:=le_trans (Fintype.card_subtype_le _) hX
  obtain ⟨M,hpos,hdis,hcov,hlow,hup⟩:=hmatch n hn I V A J E R w σ target τ t Kᵢ g S hW hA hJ hsize hw htarget hload herror hpair hsum (fun j=>j.property) hg hmass
  refine ⟨M,hpos,hdis,?_,hlow,hup⟩
  intro x hx
  exact hcov ⟨x,hx⟩
end Oberwolfach
