module

public import Oberwolfach.MarkedBoundaryNeighbourhoods
public import Oberwolfach.IndexedSupportBounds

@[expose] public section

/-! The supports used by the mixed selector are subsets of the actual
marked boundary supports. Distinct row roots and hubs are counted once,
including when their classes are chosen after sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K J I:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [Fintype J] [Fintype I] [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  [DecidableEq J] [DecidableEq I]

def markedBoundaryRootEmbedding (hub:J↪U) (root:I↪V):J⊕I↪V⊕U where
  toFun:=Sum.elim (fun j=>Sum.inr (hub j)) (fun i=>Sum.inl (root i))
  inj':=by
    intro a b hab
    cases a <;> cases b
    · exact congrArg Sum.inl (hub.injective (Sum.inr.inj hab))
    · exact (Sum.inr_ne_inl hab).elim
    · exact (Sum.inl_ne_inr hab).elim
    · exact congrArg Sum.inr (root.injective (Sum.inl.inj hab))

theorem marked_boundary_selection_supports (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (H₀ HK:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (hub:J↪U) (root:I↪V) (hhub:∀ j,hub j∉Z) (hroot:∀ i,root i∉X)
    (Y:J→Finset V) (A₀ A₁ X₀ X₁:I→Finset V) (Y₀ Y₁:I→Finset U)
    (hY:∀ j,Y j⊆markedBoundarySpokeRows H₀ HK X σ (hub j))
    (hA:∀ i,A₀ i∪A₁ i∪(X₀ i∪X₁ i)⊆markedBoundaryRimNeighbours tail head ktail khead π X σ (root i))
    (hB:∀ i,Y₀ i∪Y₁ i⊆markedBoundarySpokeHubs H₀ HK Z σ (root i))
    (P M:ℝ)
    (hP:∀ x y,x≠y→((markedBoundarySupport tail head ktail khead π H₀ HK X Z σ x∩
      markedBoundarySupport tail head ktail khead π H₀ HK X Z σ y).card:ℝ)≤P)
    (hM:∀ v,((Finset.univ.filter (fun x=>v∈markedBoundarySupport tail head ktail khead π H₀ HK X Z σ x)).card:ℝ)≤M):
    let S:J⊕I→Finset (V⊕U):=Sum.elim
      (fun j=>(Y j∪(Y j).image π).image Sum.inl)
      (fun i=>ordinaryInnerVertices (A₀ i∪A₁ i∪(X₀ i∪X₁ i)) (Y₀ i∪Y₁ i))
    (∀ i j,i≠j→((S i∩S j).card:ℝ)≤P)∧
    (∀ v,((Finset.univ.filter (fun j=>v∈S j)).card:ℝ)≤M) := by
  intro S
  apply indexed_support_bounds (markedBoundarySupport tail head ktail khead π H₀ HK X Z σ)
    (markedBoundaryRootEmbedding hub root) S _ P M hP hM
  intro i
  cases i with
  | inl j=>
    change (Y j∪(Y j).image π).image Sum.inl⊆
      markedBoundarySupport tail head ktail khead π H₀ HK X Z σ (Sum.inr (hub j))
    rw [marked_boundary_support_at_hub tail head ktail khead π H₀ HK X Z σ (hub j) (hhub j)]
    exact Finset.image_subset_image (Finset.union_subset_union (hY j) (Finset.image_subset_image (hY j)))
  | inr i=>
    change ordinaryInnerVertices (A₀ i∪A₁ i∪(X₀ i∪X₁ i)) (Y₀ i∪Y₁ i)⊆
      markedBoundarySupport tail head ktail khead π H₀ HK X Z σ (Sum.inl (root i))
    rw [marked_boundary_support_at_row tail head ktail khead π H₀ HK X Z σ (root i) (hroot i)]
    exact Finset.union_subset_union
      (Finset.image_subset_image ((hA i).trans Finset.subset_union_left)) (Finset.image_subset_image (hB i))

end Oberwolfach
