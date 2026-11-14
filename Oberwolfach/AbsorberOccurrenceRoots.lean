module

public import Oberwolfach.LabelledAbsorberFactors

@[expose] public section

/-! Each recorded cycle lies in the free vertices and roots, and
contains at most one root. These facts concern the actual cycle IDs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] {c : ℕ}

theorem labelled_absorber_occurrence_subset (R : C → Finset V)
    (S : VertexAbsorberTemplate c) (X : Finset V) (D : LabelledCycleRecord R S.val X)
    (o : Fin c ⊕ Fin (c+1)) : R (D.2 o).val⊆labelledAbsorberFree R S X D∪X := by
  intro v hv
  rw [(D.2 o).property] at hv
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
  rcases j with j | j
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  · exact Finset.mem_union_right _ (rootedLabelMap_root_mem X D.1 j)

theorem labelled_absorber_occurrence_root_intersection (R : C → Finset V)
    (S : VertexAbsorberTemplate c) (X : Finset V) (D : LabelledCycleRecord R S.val X)
    (o : Fin c ⊕ Fin (c+1)) :
    R (D.2 o).val∩X=(rootLabelPositions (S.val o)).image (fun i => D.1.val (Sum.inr i)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨hv,hx⟩ := Finset.mem_inter.mp hv
    rw [(D.2 o).property] at hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    rcases j with j | j
    · have hf : D.1.val (Sum.inl j)∈labelledAbsorberFree R S X D :=
        Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
      exact False.elim (Finset.disjoint_left.mp (labelled_absorber_factors R S X D).1 hf hx)
    · exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩
  · intro hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_inter.mpr
    refine ⟨?_,rootedLabelMap_root_mem X D.1 j⟩
    rw [(D.2 o).property]
    exact Finset.mem_image.mpr ⟨Sum.inr j,(Finset.mem_filter.mp hj).2,rfl⟩

theorem labelled_absorber_occurrence_root_unique (R : C → Finset V)
    (S : VertexAbsorberTemplate c) (X : Finset V) (D : LabelledCycleRecord R S.val X)
    (o : Fin c ⊕ Fin (c+1)) (x y : V)
    (hx : x∈R (D.2 o).val) (hy : y∈R (D.2 o).val) (hxX : x∈X) (hyX : y∈X) : x=y := by
  have hcard : (R (D.2 o).val∩X).card ≤ 1 := by
    rw [labelled_absorber_occurrence_root_intersection R S X D o]
    exact Finset.card_image_le.trans (S.property.2.2.2.2.2 o)
  exact Finset.card_le_one.mp hcard x (Finset.mem_inter.mpr ⟨hx,hxX⟩)
    y (Finset.mem_inter.mpr ⟨hy,hyX⟩)

end Oberwolfach
