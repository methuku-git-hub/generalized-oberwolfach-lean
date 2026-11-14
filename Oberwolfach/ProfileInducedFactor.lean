module

public import Oberwolfach.ProfileFactorExtraction
public import Oberwolfach.AbsorberProfileSampling
public import Oberwolfach.ProfileRestrictionCounts
public import Oberwolfach.AbsorberFamilyRestriction
public import Oberwolfach.InducedResourceWeights

@[expose] public section

/-! Factor extraction on a prescribed class-profile subset of the
ambient vertices, with the original resource identifiers and weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I T : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T] [DecidableEq T]

theorem finset_disjoint_complement_iff {W : Type*} [Fintype W] [DecidableEq W]
    (X Y : Finset W) : Disjoint X (Finset.univ\Y) ↔ X⊆Y := by
  simp only [Finset.disjoint_left,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not]
  exact Iff.rfl

theorem profile_complement_complement_card
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    (Y : Finset (Σ i,V i)) (i : I) :
    Fintype.card (ProfileRemainingClass (Finset.univ\Y) i)=
      (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈Y)).card := by
  change Fintype.card {v : V i // (⟨i,v⟩ : Σ i,V i)∉Finset.univ\Y}=_
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not,Fintype.card_subtype]

theorem profile_factor_on_subset (a : I → ℕ) (c J : ℕ) (hc : 3 ≤ c)
    (ha : ∀ i,1 ≤ a i) (hsize : ∑ i,a i=c)
    (S : T → VertexAbsorberTemplate c) (a₀ b B : ℝ)
    (ha₀ : 0 < a₀) (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ η : ℝ,0 < η ∧ ∃ k₀ : ℕ,∀ k : ℕ,k₀ ≤ k →
      ∀ (V : I → Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (C : Type) [Fintype C] [DecidableEq C],
      ∀ (R : C → Finset (Σ i,V i)) (w : C → ℝ) (Y : Finset (Σ i,V i)),
      (∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈Y)).card=a i*k) →
      (∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) →
      (∀ U : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=U} ≤ J) →
      (∀ C₀,b/(k:ℝ)^(c-1) ≤ w C₀ ∧ w C₀ ≤ B/(k:ℝ)^(c-1)) →
      (∀ v∈Y,|1-hypergraphWeightedDegree R (inducedResourceWeight R w Y) v| ≤ η) →
      (∀ σ : ∀ i,FixedSubset (V i) (a i),profileRootSet σ⊆Y →
        a₀*(k:ℝ)^(c*c) ≤ absorberGroundCount R S (profileRootSet σ) Y) →
      HasResourceDecomposition R Y := by
  obtain ⟨η,hη,k₀,hf⟩ := profile_factor_extraction a c J hc ha hsize S a₀ b B ha₀ hb hB
  refine ⟨η,hη,k₀,?_⟩
  intro k hk V _ _ C _ _ R w Y hY hR hJ hw herr habs
  let Z := Finset.univ\Y
  let V' := ProfileRemainingClass Z
  let e := profileComplementEmbedding Z
  let C' := RestrictedResource R e
  let R' := restrictedResourceSet R e
  let w' := fun D : C' => w D.val
  have he : Finset.univ.image e=Y := by
    rw [profileComplementEmbedding_univ]
    dsimp [Z]
    ext v;simp
  have hemem (v : Σ i,V' i) : e v∈Y := by
    rw [← he]
    exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
  have hn (i) : Fintype.card (V' i)=a i*k :=
    (profile_complement_complement_card Y i).trans (hY i)
  have hR' (D : C') (i) :
      (Finset.univ.filter (fun v : V' i => (⟨i,v⟩ : Σ i,V' i)∈R' D)).card=a i :=
    (profile_restricted_resource_class_card R Z D i).trans (hR D.val i)
  have herr' (v : Σ i,V' i) : |1-hypergraphWeightedDegree R' w' v| ≤ η := by
    have hh := profile_restricted_resource_degree R Z w v
    have hew : vertexRestrictedWeight R w Z=inducedResourceWeight R w Y := by
      funext D
      simp only [vertexRestrictedWeight,inducedResourceWeight,Z,finset_disjoint_complement_iff]
    rw [hew] at hh
    change |1-hypergraphWeightedDegree R' w' v| ≤ _
    rw [hh]
    exact herr (e v) (hemem v)
  have habs' (ρ : ∀ i,FixedSubset (V' i) (a i)) :
      a₀*(k:ℝ)^(c*c) ≤ Fintype.card (LabelledAbsorberFamily R' S (profileRootSet ρ)) := by
    let X := (profileRootSet ρ).image e
    have hX (i) : (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈X)).card=a i := by
      rw [profileComplementEmbedding_class_card]
      exact profileRootSet_class_card ρ i
    obtain ⟨σ,hσ⟩ := exists_profile_root_of_class_sizes a X hX
    have hXY : X⊆Y := by
      intro x hx
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
      exact hemem v
    have hc₀ := habs σ (hσ.symm ▸ hXY)
    rw [hσ] at hc₀
    have hcount := restricted_absorber_avoiding_card R e S (profileRootSet ρ) Z
      (profileComplementEmbedding_range Z)
    have hecount : Fintype.card {D : LabelledAbsorberFamily R S X //
        Disjoint (labelledAbsorberFree R (S D.1) X D.2) Z}=
        Fintype.card {D : LabelledAbsorberFamily R S X //
          labelledAbsorberFree R (S D.1) X D.2⊆Y} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun D => finset_disjoint_complement_iff _ Y)
    change Fintype.card {D : LabelledAbsorberFamily R S X //
        Disjoint (labelledAbsorberFree R (S D.1) X D.2) Z} ≤ _ at hcount
    rw [hecount] at hcount
    apply hc₀.trans
    unfold absorberGroundCount
    exact_mod_cast hcount
  have hfactor := hf k hk V' C' hn R' w' hR' (restricted_resource_multiplicity R e J hJ)
    (fun D => hw D.val) herr' habs'
  have hlift := restricted_resource_decomposition_lift R e Finset.univ hfactor
  rw [he] at hlift
  exact hlift

end Oberwolfach
