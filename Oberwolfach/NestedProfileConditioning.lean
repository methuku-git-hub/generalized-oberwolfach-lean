module

public import Oberwolfach.ConditionedProfileGeometry
public import Oberwolfach.ProfileRestrictionCounts

@[expose] public section

/-! Sampling after a fixed deletion and then conditioning on additional
roots removes the union of those sets, in the original class labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profileRootFreeEmbedding_range (T : ∀ i,Finset (V i)) (v : Σ i,V i) :
    (∃ w,profileRootFreeEmbedding T w=v) ↔ v∉Finset.univ.sigma T := by
  have hh := Finset.ext_iff.mp (profileRootFreeEmbedding_complement T) v
  simpa only [Finset.mem_map,Finset.mem_univ,true_and,Finset.mem_sdiff] using hh

theorem nested_profile_embedding_range (F : Finset (Σ i,V i))
    (T : ∀ i,Finset (ProfileRemainingClass F i)) (v : Σ i,V i) :
    (∃ w,((profileRootFreeEmbedding T).trans (profileComplementEmbedding F)) w=v) ↔
      v∉F∪(Finset.univ.sigma T).map (profileComplementEmbedding F) := by
  let e := profileComplementEmbedding F
  constructor
  · rintro ⟨w,rfl⟩ h
    rcases Finset.mem_union.mp h with hF | hT
    · exact (profileComplementEmbedding_range F _).mp ⟨profileRootFreeEmbedding T w,rfl⟩ hF
    · obtain ⟨u,hu,heu⟩ := Finset.mem_map.mp hT
      have heq : u=profileRootFreeEmbedding T w := e.injective heu
      subst u
      exact (profileRootFreeEmbedding_range T _).mp ⟨w,rfl⟩ hu
  · intro hv
    have hvF : v∉F := fun h => hv (Finset.mem_union_left _ h)
    obtain ⟨u,rfl⟩ := (profileComplementEmbedding_range F v).mpr hvF
    have hu : u∉Finset.univ.sigma T := by
      intro h
      exact hv (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨u,h,rfl⟩))
    obtain ⟨w,rfl⟩ := (profileRootFreeEmbedding_range T u).mpr hu
    exact ⟨w,rfl⟩

theorem nested_profile_embedding_class (F : Finset (Σ i,V i))
    (T : ∀ i,Finset (ProfileRemainingClass F i))
    (v : Σ i,{u : ProfileRemainingClass F i // u∉T i}) :
    (((profileRootFreeEmbedding T).trans (profileComplementEmbedding F)) v).1=v.1 := rfl

theorem nested_profile_remaining_card (F : Finset (Σ i,V i))
    (T : ∀ i,Finset (ProfileRemainingClass F i)) (i : I) :
    Fintype.card {v : ProfileRemainingClass F i // v∉T i}=
      Fintype.card (V i)-
        (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈F)).card-(T i).card := by
  rw [Fintype.card_subtype_compl,Fintype.card_coe,profileRemainingClass_card]

end Oberwolfach
