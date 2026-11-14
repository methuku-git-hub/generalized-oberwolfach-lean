module

public import Oberwolfach.BoundarySupportChanges

@[expose] public section

/-! Selection supports inherit overlap and membership bounds from their
actual distinct outside indices. Subsets may be chosen after the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W J:Type*} [Fintype V] [Fintype W] [Fintype J]
  [DecidableEq V] [DecidableEq W] [DecidableEq J]

theorem indexed_support_memberships_le (S:W→Finset V) (root:J↪W) (T:J→Finset V)
    (hs:∀ j,T j⊆S (root j)) (v:V):
    (Finset.univ.filter (fun j=>v∈T j)).card≤(Finset.univ.filter (fun x=>v∈S x)).card := by
  have hi:(Finset.univ.filter (fun j=>v∈T j)).image root⊆Finset.univ.filter (fun x=>v∈S x) := by
    intro x hx
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs j (Finset.mem_filter.mp hj).2⟩
  have hh:=Finset.card_le_card hi
  simpa only [Finset.card_image_of_injective _ root.injective] using hh

theorem indexed_support_bounds (S:W→Finset V) (root:J↪W) (T:J→Finset V)
    (hs:∀ j,T j⊆S (root j)) (P M:ℝ)
    (hP:∀ x y,x≠y→((S x∩S y).card:ℝ)≤P)
    (hM:∀ v,((Finset.univ.filter (fun x=>v∈S x)).card:ℝ)≤M):
    (∀ i j,i≠j→((T i∩T j).card:ℝ)≤P)∧
    (∀ v,((Finset.univ.filter (fun j=>v∈T j)).card:ℝ)≤M) := by
  refine ⟨?_,?_⟩
  · intro i j hij
    exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_inter (hs i) (hs j)))).trans
      (hP _ _ (fun he=>hij (root.injective he)))
  · intro v
    exact (Nat.cast_le.mpr (indexed_support_memberships_le S root T hs v)).trans (hM v)

end Oberwolfach
