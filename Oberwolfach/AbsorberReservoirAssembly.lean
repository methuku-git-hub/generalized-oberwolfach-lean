module

public import Oberwolfach.ResourceTransformers
public import Mathlib.Combinatorics.Hall.Basic

@[expose] public section

/-! Assigning disjoint absorber configurations to disjoint root sets.
The conclusion is an exact partition of vertices (or physical resources),
not merely a cardinality identity. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I J E W : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [DecidableEq E] [DecidableEq W]

theorem injective_assignment_of_many_choices (P : I → J → Prop)
    (hP : ∀ i,Fintype.card I ≤ (Finset.univ.filter (P i)).card) :
    ∃ f : I → J,Function.Injective f ∧ ∀ i,P i (f i) := by
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective P).mp
  intro A
  by_cases hA : A.Nonempty
  · obtain ⟨i,hi⟩ := hA
    have hsub : Finset.univ.filter (P i) ⊆ Finset.univ.filter (fun j => ∃ a∈A,P a j) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hi,(Finset.mem_filter.mp hj).2⟩
    exact (Finset.card_le_univ A).trans ((hP i).trans (Finset.card_le_card hsub))
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [he]

theorem assigned_absorber_reservoir (R : W → Finset E) (X : I → Finset E) (A : J → Finset E)
    (hXX : ∀ i j,i≠j → Disjoint (X i) (X j))
    (hAA : ∀ i j,i≠j → Disjoint (A i) (A j))
    (hXA : ∀ i j,Disjoint (X i) (A j))
    (hA : ∀ j,HasResourceDecomposition R (A j))
    (f : I → J) (hf : Function.Injective f)
    (habs : ∀ i,HasResourceDecomposition R (A (f i)∪X i)) :
    IsResourceAbsorber R (Finset.univ.biUnion X) (Finset.univ.biUnion A) := by
  have hdisj : Disjoint (Finset.univ.biUnion A) (Finset.univ.biUnion X) := by
    apply Finset.disjoint_left.mpr
    intro e he hx
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp he
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.disjoint_left.mp (hXA i j)) hi hj
  refine ⟨hdisj,resource_decomposition_biUnion R A Finset.univ
    (fun j _ => hA j) (fun i _ j _ h => hAA i j h),?_⟩
  let T (i : I) := A (f i)∪X i
  let U := Finset.univ\Finset.univ.image f
  have hT : HasResourceDecomposition R (Finset.univ.biUnion T) := by
    apply resource_decomposition_biUnion R T Finset.univ (fun i _ => habs i)
    intro i _ j _ hij
    apply Finset.disjoint_union_left.mpr
    constructor
    · exact Finset.disjoint_union_right.mpr ⟨hAA (f i) (f j) (fun h => hij (hf h)),(hXA j (f i)).symm⟩
    · exact Finset.disjoint_union_right.mpr ⟨hXA i (f j),hXX i j hij⟩
  have hU : HasResourceDecomposition R (U.biUnion A) :=
    resource_decomposition_biUnion R A U (fun j _ => hA j) (fun i _ j _ h => hAA i j h)
  have hTU : Disjoint (Finset.univ.biUnion T) (U.biUnion A) := by
    apply Finset.disjoint_left.mpr
    intro e he hu
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
    obtain ⟨j,hj,hje⟩ := Finset.mem_biUnion.mp hu
    have hn : f i≠j := by
      intro he
      exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩)
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (Finset.disjoint_left.mp (hAA (f i) j hn)) hi hje
    · exact (Finset.disjoint_left.mp (hXA i j)) hi hje
  have heq : (Finset.univ.biUnion T)∪U.biUnion A=(Finset.univ.biUnion A)∪Finset.univ.biUnion X := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
        rcases Finset.mem_union.mp hi with hi | hi
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨f i,Finset.mem_univ _,hi⟩)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩)
      · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp he
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hj⟩)
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp he
        by_cases hf' : j∈Finset.univ.image f
        · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf'
          exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_union_left _ hj⟩)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hf'⟩,hj⟩)
      · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_union_right _ hi⟩)
  rw [← heq]
  exact resource_decomposition_union R _ _ hT hU hTU

theorem absorber_reservoir_of_many_choices (R : W → Finset E) (X : I → Finset E) (A : J → Finset E)
    (hXX : ∀ i j,i≠j → Disjoint (X i) (X j))
    (hAA : ∀ i j,i≠j → Disjoint (A i) (A j))
    (hXA : ∀ i j,Disjoint (X i) (A j))
    (hA : ∀ j,HasResourceDecomposition R (A j))
    (hchoices : ∀ i,Fintype.card I ≤
      (Finset.univ.filter (fun j => HasResourceDecomposition R (A j∪X i))).card) :
    IsResourceAbsorber R (Finset.univ.biUnion X) (Finset.univ.biUnion A) := by
  obtain ⟨f,hf,habs⟩ := injective_assignment_of_many_choices
    (fun i j => HasResourceDecomposition R (A j∪X i)) hchoices
  exact assigned_absorber_reservoir R X A hXX hAA hXA hA f hf habs

end Oberwolfach
