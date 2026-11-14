module

public import Oberwolfach.AbsorberFreeRecords

@[expose] public section

/-! The free configuration has an exact internal factor and the required
class proportions before any root set is assigned to it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] {c : ℕ}

theorem template_zero_free_partition (S : VertexAbsorberTemplate c) :
    (∀ i j : Fin c,i≠j → Disjoint (freeLabelPositions (S.val (Sum.inl i)))
      (freeLabelPositions (S.val (Sum.inl j)))) ∧
    Finset.univ.biUnion (fun i : Fin c => freeLabelPositions (S.val (Sum.inl i)))=Finset.univ := by
  constructor
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact Finset.disjoint_left.mp (S.property.2.1 i j hij)
      (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2
  · apply Finset.eq_univ_of_forall
    intro v
    have hm : Sum.inl v∈Finset.univ.biUnion (fun i : Fin c => S.val (Sum.inl i)) := by
      rw [S.property.2.2.2.1]
      exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩

def freeAbsorberVertices (R : C → Finset V) (S : VertexAbsorberTemplate c)
    (F : FreeAbsorberRecord R S) : Finset V := Finset.univ.image F.1

theorem free_absorber_internal_factor (R : C → Finset V) (S : VertexAbsorberTemplate c)
    (F : FreeAbsorberRecord R S) : HasResourceDecomposition R (freeAbsorberVertices R S F) := by
  obtain ⟨hd,he⟩ := template_zero_free_partition S
  obtain ⟨hD,hE⟩ := labelled_factor_image (fun i : Fin c => freeLabelPositions (S.val (Sum.inl i)))
    Finset.univ hd he F.1 F.1.injective R (fun i => (F.2 i).val) (fun i => (F.2 i).property)
  exact ⟨_,hD,hE⟩

theorem free_absorber_vertex_count (R : C → Finset V) (S : VertexAbsorberTemplate c)
    (F : FreeAbsorberRecord R S) : (freeAbsorberVertices R S F).card=c*c := by
  rw [freeAbsorberVertices,Finset.card_image_of_injective _ F.1.injective]
  simp

theorem free_absorber_indexed_partition (R : C → Finset V) (S : VertexAbsorberTemplate c)
    (F : FreeAbsorberRecord R S) :
    (∀ i j : Fin c,i≠j → Disjoint (R (F.2 i).val) (R (F.2 j).val)) ∧
      Finset.univ.biUnion (fun i : Fin c => R (F.2 i).val)=freeAbsorberVertices R S F := by
  obtain ⟨hd,he⟩ := template_zero_free_partition S
  constructor
  · intro i j hij
    rw [(F.2 i).property,(F.2 j).property]
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hw
    have hh := F.1.injective heq
    subst y
    exact Finset.disjoint_left.mp (hd i j hij) hx hy
  · ext v
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,freeAbsorberVertices,Finset.mem_image]
    constructor
    · rintro ⟨i,hi⟩
      rw [(F.2 i).property] at hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j,rfl⟩
    · rintro ⟨j,rfl⟩
      have hj : j∈Finset.univ.biUnion (fun i : Fin c => freeLabelPositions (S.val (Sum.inl i))) := by
        rw [he];exact Finset.mem_univ _
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hj
      refine ⟨i,?_⟩
      rw [(F.2 i).property]
      exact Finset.mem_image.mpr ⟨j,hi,rfl⟩

theorem free_absorber_class_card {I : Type*} [DecidableEq I]
    (R : C → Finset V) (S : VertexAbsorberTemplate c) (F : FreeAbsorberRecord R S)
    (κ : V → I) (a : I → ℕ) (hR : ∀ C₀ i,((R C₀).filter (fun v => κ v=i)).card=a i) (i : I) :
    ((freeAbsorberVertices R S F).filter (fun v => κ v=i)).card=c*a i := by
  obtain ⟨hd,he⟩ := free_absorber_indexed_partition R S F
  have he' : (freeAbsorberVertices R S F).filter (fun v => κ v=i)=
      Finset.univ.biUnion (fun j : Fin c => (R (F.2 j).val).filter (fun v => κ v=i)) := by
    rw [← he]
    ext v
    simp only [Finset.mem_filter,Finset.mem_biUnion,Finset.mem_univ,true_and]
    aesop
  rw [he',Finset.card_biUnion (by
    intro j _ k _ hjk
    exact (hd j k hjk).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  simp only [hR,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

end Oberwolfach
