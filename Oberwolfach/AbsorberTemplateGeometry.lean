module

public import Oberwolfach.LabelledCycleRecords
public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! Finite labelled positions and the two partitions of a vertex absorber.
The at-most-one-root condition is imposed on each cycle occurrence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] {h c : ℕ}

def rootLabelPositions (S : Finset (Fin h ⊕ Fin c)) : Finset (Fin c) :=
  Finset.univ.filter (fun i => Sum.inr i∈S)

theorem label_positions_card (S : Finset (Fin h ⊕ Fin c)) :
    (freeLabelPositions S).card+(rootLabelPositions S).card=S.card := by
  have he : S=(freeLabelPositions S).image Sum.inl ∪ (rootLabelPositions S).image Sum.inr := by
    ext j;rcases j with j | j <;> simp [freeLabelPositions,rootLabelPositions]
  have hd : Disjoint ((freeLabelPositions S).image Sum.inl) ((rootLabelPositions S).image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp hz'
    cases he
  conv_rhs => rw [he,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ Sum.inl_injective,Finset.card_image_of_injective _ Sum.inr_injective]

theorem rooted_label_cycle_disjoint (X Y : Finset V) (S : Finset (Fin h ⊕ Fin c))
    (f : RootedLabelMap V h c X) (he : S.image f.val=Y) (hXY : Disjoint Y X) :
    rootLabelPositions S=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hs : f.val (Sum.inr j)∈Y := by
    rw [← he]
    exact Finset.mem_image.mpr ⟨Sum.inr j,(Finset.mem_filter.mp hj).2,rfl⟩
  exact Finset.disjoint_left.mp hXY hs (rootedLabelMap_root_mem X f j)

def IsVertexAbsorberTemplate (c : ℕ)
    (S : (Fin c ⊕ Fin (c+1)) → Finset (Fin (c*c) ⊕ Fin c)) : Prop :=
  (∀ o,(S o).card=c) ∧
  (∀ i j : Fin c,i≠j → Disjoint (S (Sum.inl i)) (S (Sum.inl j))) ∧
  (∀ i j : Fin (c+1),i≠j → Disjoint (S (Sum.inr i)) (S (Sum.inr j))) ∧
  (Finset.univ.biUnion (fun i : Fin c => S (Sum.inl i))=Finset.univ.image Sum.inl) ∧
  (Finset.univ.biUnion (fun i : Fin (c+1) => S (Sum.inr i))=Finset.univ) ∧
  (∀ o,(rootLabelPositions (S o)).card ≤ 1)

abbrev VertexAbsorberTemplate (c : ℕ) :=
  {S : (Fin c ⊕ Fin (c+1)) → Finset (Fin (c*c) ⊕ Fin c) // IsVertexAbsorberTemplate c S}

theorem labelled_factor_image {I P : Type*} [Fintype I] [DecidableEq P]
    (S : I → Finset P) (A : Finset P)
    (hd : ∀ i j,i≠j → Disjoint (S i) (S j)) (he : Finset.univ.biUnion S=A)
    (f : P → V) (hf : Function.Injective f) (R : C → Finset V) (g : I → C)
    (hg : ∀ i,R (g i)=(S i).image f) :
    (∀ a∈Finset.univ.image g,∀ b∈Finset.univ.image g,a≠b → Disjoint (R a) (R b)) ∧
      (Finset.univ.image g).biUnion R=A.image f := by
  constructor
  · intro a ha b hb hab
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    rw [hg,hg]
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hw
    have heq' := hf heq
    subst y
    exact Finset.disjoint_left.mp (hd i j (fun hij => hab (congrArg g hij))) hx hy
  · ext v
    simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨C₀,⟨i,rfl⟩,hv⟩
      rw [hg] at hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      refine ⟨x,?_,rfl⟩
      rw [← he]
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩
    · rintro ⟨x,hx,rfl⟩
      rw [← he] at hx
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
      refine ⟨g i,⟨i,rfl⟩,?_⟩
      rw [hg]
      exact Finset.mem_image.mpr ⟨x,hi,rfl⟩

end Oberwolfach
