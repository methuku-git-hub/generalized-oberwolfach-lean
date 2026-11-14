module

public import Oberwolfach.SigmaClassCounts
public import Oberwolfach.RootOmittedClassCounts

@[expose] public section

/-! Class counts are preserved by embeddings that preserve the class
index, whenever the set being counted lies in the embedding's image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V W : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    [∀ i,Fintype (W i)] [∀ i,DecidableEq (W i)]

theorem profile_embedding_preimage_class_card (e : (Σ i,W i) ↪ (Σ i,V i))
    (he : ∀ v,(e v).1=v.1) (F : Finset (Σ i,V i))
    (hF : ∀ v∈F,∃ w,e w=v) (i : I) :
    (Finset.univ.filter (fun w : W i => e ⟨i,w⟩∈F)).card=
      (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈F)).card := by
  let A : Finset (Σ i,W i) := Finset.univ.filter (fun w => e w∈F)
  have hmap : A.map e=F := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hv
      exact (Finset.mem_filter.mp hw).2
    · intro hv
      obtain ⟨w,rfl⟩ := hF v hv
      exact Finset.mem_map.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
  have hfilter : (A.filter (fun w => w.1=i)).map e=F.filter (fun v => v.1=i) := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨hw,hi⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).2,(he w).trans hi⟩
    · intro hv
      obtain ⟨hv,hi⟩ := Finset.mem_filter.mp hv
      rw [← hmap] at hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hv
      exact Finset.mem_map.mpr ⟨w,Finset.mem_filter.mpr ⟨hw,(he w).symm.trans hi⟩,rfl⟩
  have hcard := congrArg Finset.card hfilter
  rw [Finset.card_map,sigma_finset_class_card] at hcard
  rw [sigma_finset_class_card F i] at hcard
  simpa [A] using hcard

theorem profile_embedding_root_omitted_card (e : (Σ i,W i) ↪ (Σ i,V i))
    (he : ∀ v,(e v).1=v.1) (F : Finset (Σ i,V i)) (v : Σ i,V i) (hv : v∈F)
    (hF : ∀ x∈F.erase v,∃ w,e w=x) (i : I) :
    (Finset.univ.filter (fun w : W i => e ⟨i,w⟩∈F.erase v)).card=
      (Finset.univ.filter (fun u : V i => (⟨i,u⟩ : Σ i,V i)∈F)).card-
        (if v.1=i then 1 else 0) := by
  rw [profile_embedding_preimage_class_card e he (F.erase v) hF i]
  exact profile_erase_class_card F v hv i

end Oberwolfach
