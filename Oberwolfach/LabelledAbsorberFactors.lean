module

public import Oberwolfach.AbsorberTemplateGeometry
public import Oberwolfach.AbsorberTrades

@[expose] public section

/-! The two actual vertex partitions of a labelled absorber record.
Free vertices and roots have disjoint images because the full label map
is injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] {c : ℕ}

def labelledAbsorberZero (R : C → Finset V) (S : VertexAbsorberTemplate c) (X : Finset V)
    (D : LabelledCycleRecord R S.val X) : Finset C :=
  Finset.univ.image (fun i : Fin c => (D.2 (Sum.inl i)).val)

def labelledAbsorberOne (R : C → Finset V) (S : VertexAbsorberTemplate c) (X : Finset V)
    (D : LabelledCycleRecord R S.val X) : Finset C :=
  Finset.univ.image (fun i : Fin (c+1) => (D.2 (Sum.inr i)).val)

def labelledAbsorberFree (R : C → Finset V) (S : VertexAbsorberTemplate c) (X : Finset V)
    (D : LabelledCycleRecord R S.val X) : Finset V :=
  Finset.univ.image (fun i : Fin (c*c) => D.1.val (Sum.inl i))

theorem labelled_absorber_factors (R : C → Finset V) (S : VertexAbsorberTemplate c) (X : Finset V)
    (D : LabelledCycleRecord R S.val X) :
    Disjoint (labelledAbsorberFree R S X D) X ∧
    (∀ a∈labelledAbsorberZero R S X D,∀ b∈labelledAbsorberZero R S X D,a≠b → Disjoint (R a) (R b)) ∧
    (labelledAbsorberZero R S X D).biUnion R=labelledAbsorberFree R S X D ∧
    (∀ a∈labelledAbsorberOne R S X D,∀ b∈labelledAbsorberOne R S X D,a≠b → Disjoint (R a) (R b)) ∧
    (labelledAbsorberOne R S X D).biUnion R=labelledAbsorberFree R S X D∪X := by
  have h₀ := labelled_factor_image (fun i : Fin c => S.val (Sum.inl i))
    (Finset.univ.image Sum.inl) S.property.2.1 S.property.2.2.2.1 D.1.val D.1.property.1 R
    (fun i => (D.2 (Sum.inl i)).val) (fun i => (D.2 (Sum.inl i)).property)
  have h₁ := labelled_factor_image (fun i : Fin (c+1) => S.val (Sum.inr i))
    Finset.univ S.property.2.2.1 S.property.2.2.2.2.1 D.1.val D.1.property.1 R
    (fun i => (D.2 (Sum.inr i)).val) (fun i => (D.2 (Sum.inr i)).property)
  have hf : (Finset.univ.image Sum.inl).image D.1.val=labelledAbsorberFree R S X D := by
    simp [labelledAbsorberFree,Finset.image_image,Function.comp_def]
  have hu : Finset.univ.image D.1.val=labelledAbsorberFree R S X D∪X := by
    ext v
    constructor
    · intro hv
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
      rcases j with j | j
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
      · exact Finset.mem_union_right _ (rootedLabelMap_root_mem X D.1 j)
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_image.mpr ⟨Sum.inl j,Finset.mem_univ _,rfl⟩
      · have hx := D.1.property.2
        rw [← hx] at hv
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_image.mpr ⟨Sum.inr j,Finset.mem_univ _,rfl⟩
  refine ⟨?_,h₀.1,h₀.2.trans hf,h₁.1,h₁.2.trans hu⟩
  apply Finset.disjoint_left.mpr
  intro v hv hx
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  have hroot := D.1.property.2
  have hx' : D.1.val (Sum.inl i)∈Finset.univ.image (fun j => D.1.val (Sum.inr j)) := by
    simpa only [hroot] using hx
  obtain ⟨j,_,he⟩ := Finset.mem_image.mp hx'
  have hh := D.1.property.1 he
  cases hh

theorem labelled_absorber_trade_incidence (R : C → Finset V) (S : VertexAbsorberTemplate c)
    (X : Finset V) (D : LabelledCycleRecord R S.val X) (v : V) :
    (∑ C₀,if v∈R C₀ then absorberTrade (labelledAbsorberZero R S X D)
      (labelledAbsorberOne R S X D) C₀ else 0)=if v∈X then 1 else 0 := by
  obtain ⟨hd,h₀,he₀,h₁,he₁⟩ := labelled_absorber_factors R S X D
  exact absorberTrade_incidence R X _ hd _ _ h₀ he₀ h₁ he₁ v

end Oberwolfach
