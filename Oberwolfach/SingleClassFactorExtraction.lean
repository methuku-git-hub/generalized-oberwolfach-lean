module

public import Oberwolfach.SupportedResourceFactors
public import Oberwolfach.PairedProfileFactor

@[expose] public section

/-! Exact factor extraction on a specified finite subset, with one vertex
class. The indexed resources and their supplied weights are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem single_class_factor_extraction (r J : ℕ) [NeZero r] (hr : 3≤r) (α b B : ℝ)
    (hα : 0<α) (hb : 0<b) (hB : 0≤B) :
    ∃ η : ℝ,0<η ∧ ∃ k₀ : ℕ,∀ k : ℕ,k₀≤k →
      ∀ (W C : Type) [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C],
      ∀ (T : Finset W) (R : C→Finset W) (wt : C→ℝ),T.card=r*k →
      (∀ c,R c⊆T) → (∀ c,(R c).card=r) →
      (∀ Y : Finset W,Fintype.card {c // R c=Y}≤J) →
      (∀ c,b/(k:ℝ)^(r-1)≤wt c ∧ wt c≤B/(k:ℝ)^(r-1)) →
      (∀ v∈T,|1-hypergraphWeightedDegree R wt v|≤η) →
      (∀ X : Finset W,X⊆T → X.card=r → α*(k:ℝ)^(r*r)≤
        Fintype.card (LabelledCycleRecord R (pairedAbsorberTemplate r).val X)) →
      HasResourceDecomposition R T := by
  let S : Unit→VertexAbsorberTemplate r := fun _=>pairedAbsorberTemplate r
  obtain ⟨η,hη,k₀,hfactor⟩ := supported_profile_factor_extraction (fun _ : Unit=>r) r J hr
    (fun _=>by omega) (by simp) S α b B hα hb hB
  refine ⟨η,hη,k₀,?_⟩
  intro k hk W C _ _ _ _ T R wt hT hsupp hR hJ hw herr habs
  let V : Unit→Type := fun _=>T
  let e : (Σ i,V i) ↪ W := ⟨fun v=>v.2.val,by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    cases i;cases j
    exact congrArg (Sigma.mk ()) (Subtype.ext h)⟩
  have heT : Finset.univ.image e=T := by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨i,x⟩,rfl⟩;exact x.property
    · intro hv;exact ⟨⟨(),⟨v,hv⟩⟩,rfl⟩
  have hprofile (c : C) (i : Unit) :
      (Finset.univ.filter (fun v : V i=>e ⟨i,v⟩∈R c)).card=r := by
    rw [← hR c]
    apply Finset.card_bij (fun v _=>v.val)
    · intro v hv;exact (Finset.mem_filter.mp hv).2
    · intro v _ w _ h;exact Subtype.ext h
    · intro v hv
      exact ⟨⟨v,hsupp c hv⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
  have hh := hfactor k hk V W C (fun _=>by simpa only [V,Fintype.card_coe] using hT) e R wt
    (fun c v hv=>⟨⟨(),⟨v,hsupp c hv⟩⟩,rfl⟩) hprofile hJ hw
    (fun v=>herr _ v.2.property) (by
      intro σ
      let X := (profileRootSet σ).image e
      have hXT : X⊆T := by
        intro v hv;obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp hv;exact z.2.property
      have hXr : X.card=r := by
        rw [Finset.card_image_of_injective _ e.injective,profileRootSet_card]
        simp
      have hc := habs X hXT hXr
      let f : LabelledCycleRecord R (pairedAbsorberTemplate r).val X→LabelledAbsorberFamily R S X := fun D=>⟨(),D⟩
      have hi : Function.Injective f := by
        intro D E h;exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
      exact hc.trans (by exact_mod_cast Fintype.card_le_of_injective f hi))
  simpa only [heT] using hh

end Oberwolfach
