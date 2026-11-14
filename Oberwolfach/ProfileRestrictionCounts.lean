module

public import Oberwolfach.ProfileVertexRestriction
public import Oberwolfach.SigmaClassCounts

@[expose] public section

/-! Exact sizes and images of subsets of the remaining classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profileComplementEmbedding_univ (Z : Finset (Σ i,V i)) :
    Finset.univ.image (profileComplementEmbedding Z)=Finset.univ\Z := by
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_sdiff,
    profileComplementEmbedding_range]

theorem profileComplementEmbedding_image_disjoint (Z : Finset (Σ i,V i))
    (A : Finset (Σ i,ProfileRemainingClass Z i)) :
    Disjoint (A.image (profileComplementEmbedding Z)) Z := by
  apply Finset.disjoint_left.mpr
  intro v hv hz
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  exact (profileComplementEmbedding_range Z _).mp ⟨w,rfl⟩ hz

theorem profileComplementEmbedding_class_card (Z : Finset (Σ i,V i))
    (A : Finset (Σ i,ProfileRemainingClass Z i)) (i : I) :
    (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A.image (profileComplementEmbedding Z))).card=
      (Finset.univ.filter (fun v : ProfileRemainingClass Z i => (⟨i,v⟩ : Σ i,ProfileRemainingClass Z i)∈A)).card := by
  rw [← sigma_finset_class_card,← sigma_finset_class_card]
  have he : (A.image (profileComplementEmbedding Z)).filter (fun v => v.1=i)=
      (A.filter (fun v => v.1=i)).image (profileComplementEmbedding Z) := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨w,hw,rfl⟩,hi⟩
      exact ⟨w,⟨hw,hi⟩,rfl⟩
    · rintro ⟨w,⟨hw,hi⟩,rfl⟩
      exact ⟨⟨w,hw,rfl⟩,hi⟩
  rw [he,Finset.card_image_of_injective _ (profileComplementEmbedding Z).injective]

end Oberwolfach
