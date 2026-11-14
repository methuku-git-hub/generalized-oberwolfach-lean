module

public import Oberwolfach.ProfileFactorExtraction
public import Oberwolfach.AbsorberFamilyRestriction

@[expose] public section

/-! Factor extraction on an embedded subset of the original vertex set.
All cycle identifiers and weights remain in the parent family; no ambient
permutation or graph structure is restricted to a new self-map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W Z C T : Type*} [Fintype W] [DecidableEq W] [Fintype Z] [DecidableEq Z]
    [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T] {c : ℕ}

theorem all_supported_absorber_family_card (R : C → Finset W) (e : Z ↪ W)
    (hsupp : ∀ C₀,∀ v∈R C₀,∃ z,e z=v) (S : T → VertexAbsorberTemplate c) (X : Finset Z) :
    Fintype.card (LabelledAbsorberFamily R S (X.image e))≤
      Fintype.card (LabelledAbsorberFamily (restrictedResourceSet R e) S X) := by
  let embed : LabelledAbsorberFamily R S (X.image e) → SupportedAbsorberFamily R e S X := fun D =>
    ⟨D,by
      intro j
      rcases j with j|j
      · have hv : D.2.1.val (Sum.inl j)∈labelledAbsorberFree R (S D.1) (X.image e) D.2 :=
          Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
        rw [← (labelled_absorber_factors R (S D.1) (X.image e) D.2).2.2.1] at hv
        obtain ⟨C₀,_,hv⟩ := Finset.mem_biUnion.mp hv
        exact hsupp C₀ _ hv
      · obtain ⟨z,_,hz⟩ := Finset.mem_image.mp (rootedLabelMap_root_mem (X.image e) D.2.1 j)
        exact ⟨z,hz⟩⟩
  have hi : Function.Injective embed := by
    intro D E he
    exact congrArg (fun F : SupportedAbsorberFamily R e S X => F.val) he
  exact (Fintype.card_le_of_injective embed hi).trans (restricted_absorber_family_card R e S X)

variable {I Tpl : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Tpl] [DecidableEq Tpl]

theorem supported_profile_factor_extraction (a : I → ℕ) (c J : ℕ) (hc : 3≤c)
    (ha : ∀ i,1≤a i) (hsize : ∑ i,a i=c)
    (S : Tpl → VertexAbsorberTemplate c) (α b B : ℝ)
    (hα : 0<α) (hb : 0<b) (hB : 0≤B) :
    ∃ η : ℝ,0<η ∧ ∃ k₀ : ℕ,∀ k : ℕ,k₀≤k →
      ∀ (V : I → Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (W C : Type) [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C],
      (∀ i,Fintype.card (V i)=a i*k) →
      ∀ (e : (Σ i,V i) ↪ W) (R : C → Finset W) (wt : C → ℝ),
      (∀ C₀,∀ v∈R C₀,∃ z,e z=v) →
      (∀ C₀ i,(Finset.univ.filter (fun v : V i => e ⟨i,v⟩∈R C₀)).card=a i) →
      (∀ Y : Finset W,Fintype.card {C₀ // R C₀=Y}≤J) →
      (∀ C₀,b/(k:ℝ)^(c-1)≤wt C₀ ∧ wt C₀≤B/(k:ℝ)^(c-1)) →
      (∀ v,|1-hypergraphWeightedDegree R wt (e v)|≤η) →
      (∀ σ : ∀ i,FixedSubset (V i) (a i),α*(k:ℝ)^(c*c)≤
        Fintype.card (LabelledAbsorberFamily R S ((profileRootSet σ).image e))) →
      HasResourceDecomposition R (Finset.univ.image e) := by
  obtain ⟨η,hη,k₀,hfactor⟩ := profile_factor_extraction a c J hc ha hsize S α b B hα hb hB
  refine ⟨η,hη,k₀,?_⟩
  intro k hk V _ _ W C _ _ _ _ hn e R wt hsupp hR hJ hw herr habs
  have hprofile (C₀ : RestrictedResource R e) (i : I) :
      (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈restrictedResourceSet R e C₀)).card=a i := by
    simpa only [restrictedResourceSet_mem] using hR C₀.val i
  have hdegree (v : Σ i,V i) : hypergraphWeightedDegree (restrictedResourceSet R e) (fun C₀ => wt C₀.val) v=
      hypergraphWeightedDegree R wt (e v) := by
    rw [restricted_resource_degree]
    have he : (fun C₀ => if ∀ x∈R C₀,∃ z,e z=x then wt C₀ else 0)=wt := by
      funext C₀;rw [if_pos (hsupp C₀)]
    rw [he]
  have hfactor' := hfactor k hk V (RestrictedResource R e) hn (restrictedResourceSet R e)
    (fun C₀ => wt C₀.val) hprofile (restricted_resource_multiplicity R e J hJ)
    (fun C₀ => hw C₀.val) (fun v => by rw [hdegree];exact herr v)
    (fun σ => (habs σ).trans (by exact_mod_cast all_supported_absorber_family_card R e hsupp S (profileRootSet σ)))
  exact restricted_resource_decomposition_lift R e Finset.univ hfactor'

end Oberwolfach
