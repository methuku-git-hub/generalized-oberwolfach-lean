module

public import Oberwolfach.NestedProfileConditioning
public import Oberwolfach.EmbeddedAbsorberDeletionExpectation
public import Oberwolfach.FixedSizeProfileConditioning
public import Oberwolfach.ConditionedProfileSampling

@[expose] public section

/-! The conditional absorber mean counts only free labels. Roots already
present in the conditioned sample do not change this inclusion test. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {C Tpl : Type*} [Fintype C] [DecidableEq C] [Fintype Tpl] [DecidableEq Tpl] {c : ℕ}

theorem conditional_absorber_original_mean
    (R : C → Finset (Σ i,V i)) (S : Tpl → VertexAbsorberTemplate c) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (F X : Finset (Σ i,V i)) (T : ∀ i,Finset (ProfileRemainingClass F i))
    (m : I → ℕ) (hT : ∀ i,(T i).card ≤ m i)
    [∀ i,Nonempty (FixedSubset {v : ProfileRemainingClass F i // v∉T i} (m i-(T i).card))]
    (hm : ∀ i,m i-(T i).card ≤ Fintype.card {v : ProfileRemainingClass F i // v∉T i})
    (hroot : (Finset.univ.sigma T).map (profileComplementEmbedding F)⊆X) :
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform
      (FixedSubset {v : ProfileRemainingClass F i // v∉T i} (m i-(T i).card)))
    ν.expectation (fun σ => absorberGroundCount R S X
      ((profileRootSet (fillProfileRootsAtSize T m hT σ)).map (profileComplementEmbedding F)))=
      (∏ i,((m i-(T i).card).choose (c*a i):ℝ)/
        (Fintype.card {v : ProfileRemainingClass F i // v∉T i}).choose (c*a i))*
        Fintype.card {D : LabelledAbsorberFamily R S X //
          Disjoint (labelledAbsorberFree R (S D.1) X D.2)
            (F∪(Finset.univ.sigma T).map (profileComplementEmbedding F))} := by
  let e := (profileRootFreeEmbedding T).trans (profileComplementEmbedding F)
  have hecount (σ : ∀ i,FixedSubset {v : ProfileRemainingClass F i // v∉T i} (m i-(T i).card)) :
      absorberGroundCount R S X ((profileRootSet (fillProfileRootsAtSize T m hT σ)).map (profileComplementEmbedding F))=
        absorberGroundCount R S X ((profileRootSet σ).map e) := by
    rw [fillProfileRootsAtSize_ground,Finset.map_union,Finset.map_map]
    exact absorberGroundCount_remove_fixed_roots R S X _ _ hroot
  dsimp only
  simp_rw [hecount]
  exact embedded_absorber_deletion_expectation e (nested_profile_embedding_class F T) R S a hR X
    (F∪(Finset.univ.sigma T).map (profileComplementEmbedding F)) (nested_profile_embedding_range F T)
    (fun i => m i-(T i).card) hm

end Oberwolfach
