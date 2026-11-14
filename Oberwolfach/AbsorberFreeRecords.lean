module

public import Oberwolfach.LabelledAbsorberFactors

@[expose] public section

/-! A free configuration retains the template, free label map and
internal factor. Root labels and the second factor are not retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] {c : ℕ}

theorem template_zero_root_empty (S : VertexAbsorberTemplate c) (i : Fin c) :
    rootLabelPositions (S.val (Sum.inl i))=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hm : Sum.inr j∈Finset.univ.biUnion (fun i : Fin c => S.val (Sum.inl i)) :=
    Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
  rw [S.property.2.2.2.1] at hm
  obtain ⟨x,_,he⟩ := Finset.mem_image.mp hm
  cases he

theorem template_zero_free_image (S : VertexAbsorberTemplate c) (i : Fin c)
    (f : Fin (c*c) ⊕ Fin c → V) :
    (freeLabelPositions (S.val (Sum.inl i))).image (fun j => f (Sum.inl j))=
      (S.val (Sum.inl i)).image f := by
  ext v
  constructor
  · intro hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨Sum.inl j,(Finset.mem_filter.mp hj).2,rfl⟩
  · intro hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    rcases j with j | j
    · exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩
    · have hm : j∈rootLabelPositions (S.val (Sum.inl i)) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
      rw [template_zero_root_empty] at hm
      exact (Finset.notMem_empty _ hm).elim

abbrev FreeAbsorberRecord (R : C → Finset V) (S : VertexAbsorberTemplate c) :=
  Σ f : Fin (c*c) ↪ V,∀ i : Fin c,{C₀ : C // R C₀=
    (freeLabelPositions (S.val (Sum.inl i))).image f}

def forgetAbsorberRoots (R : C → Finset V) (S : VertexAbsorberTemplate c)
    (X : Finset V) (D : LabelledCycleRecord R S.val X) : FreeAbsorberRecord R S :=
  ⟨⟨fun i => D.1.val (Sum.inl i),fun _ _ he => Sum.inl.inj (D.1.property.1 he)⟩,
    fun i => ⟨(D.2 (Sum.inl i)).val,by
      exact (D.2 (Sum.inl i)).property.trans (template_zero_free_image S i D.1.val).symm⟩⟩

theorem forgetAbsorberRoots_free_map (R : C → Finset V) (S : VertexAbsorberTemplate c)
    (X : Finset V) (D : LabelledCycleRecord R S.val X) (i : Fin (c*c)) :
    (forgetAbsorberRoots R S X D).1 i=D.1.val (Sum.inl i) := rfl

theorem forgetAbsorberRoots_zero (R : C → Finset V) (S : VertexAbsorberTemplate c)
    (X : Finset V) (D : LabelledCycleRecord R S.val X) (i : Fin c) :
    ((forgetAbsorberRoots R S X D).2 i).val=(D.2 (Sum.inl i)).val := rfl

end Oberwolfach
