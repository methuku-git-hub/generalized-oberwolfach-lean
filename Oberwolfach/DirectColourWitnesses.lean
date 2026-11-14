module

public import Oberwolfach.NibbleColourCounts

@[expose] public section

/-! One explicit direct vertex for each assigned or rejected set.
The union of these choices has size at most the number of sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def assignedDirectVertex {V C J : Type*} (Q : Finset J) (T : J → Finset V)
    (σ : V → C×Bool) (c : C) (j : assignedSetIndices Q T σ c) : V :=
  Classical.choose (Finset.mem_filter.mp j.property).2

theorem assignedDirectVertex_spec {V C J : Type*}
    (Q : Finset J) (T : J → Finset V) (σ : V → C×Bool) (c : C)
    (j : assignedSetIndices Q T σ c) :
    assignedDirectVertex Q T σ c j∈T j.val ∧
      (σ (assignedDirectVertex Q T σ c j)).1=c :=
  Classical.choose_spec (Finset.mem_filter.mp j.property).2

def rejectedDirectVertex {V C J : Type*} (G : SimpleGraph V)
    (Q : Finset J) (T : J → Finset V)
    (σ : V → C×Bool) (c : C) (j : rejectedSetIndices G Q T σ c) : V :=
  Classical.choose (Finset.mem_filter.mp j.property).2

theorem rejectedDirectVertex_spec {V C J : Type*} (G : SimpleGraph V)
    (Q : Finset J) (T : J → Finset V) (σ : V → C×Bool) (c : C)
    (j : rejectedSetIndices G Q T σ c) :
    rejectedDirectVertex G Q T σ c j∈T j.val ∧
      (σ (rejectedDirectVertex G Q T σ c j)).1=c ∧
      ¬coinColourSurvives G σ (rejectedDirectVertex G Q T σ c j) :=
  Classical.choose_spec (Finset.mem_filter.mp j.property).2

def assignedDirectVertices {V C J : Type*} (Q : Finset J) (T : J → Finset V)
    (σ : V → C×Bool) (c : C) : Finset V := by
  classical
  exact (assignedSetIndices Q T σ c).attach.image (assignedDirectVertex Q T σ c)

def rejectedDirectVertices {V C J : Type*} (G : SimpleGraph V)
    (Q : Finset J) (T : J → Finset V) (σ : V → C×Bool) (c : C) : Finset V := by
  classical
  exact (rejectedSetIndices G Q T σ c).attach.image (rejectedDirectVertex G Q T σ c)

theorem assignedDirectVertices_card {V C J : Type*}
    (Q : Finset J) (T : J → Finset V) (σ : V → C×Bool) (c : C) :
    (assignedDirectVertices Q T σ c).card≤Q.card := by
  classical
  calc
    _ ≤ (assignedSetIndices Q T σ c).attach.card := Finset.card_image_le
    _ = (assignedSetIndices Q T σ c).card := Finset.card_attach
    _ ≤ _ := Finset.card_le_card (Finset.filter_subset _ _)

theorem rejectedDirectVertices_card {V C J : Type*} (G : SimpleGraph V)
    (Q : Finset J) (T : J → Finset V) (σ : V → C×Bool) (c : C) :
    (rejectedDirectVertices G Q T σ c).card≤Q.card := by
  classical
  calc
    _ ≤ (rejectedSetIndices G Q T σ c).attach.card := Finset.card_image_le
    _ = (rejectedSetIndices G Q T σ c).card := Finset.card_attach
    _ ≤ _ := Finset.card_le_card (Finset.filter_subset _ _)

theorem assignedDirectVertices_spec {V C J : Type*}
    (Q : Finset J) (T : J → Finset V) (σ : V → C×Bool) (c : C)
    {v : V} (hv : v∈assignedDirectVertices Q T σ c) :
    (σ v).1=c ∧ ∃ j∈Q,v∈T j := by
  classical
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
  have h := assignedDirectVertex_spec Q T σ c j
  exact ⟨h.2,j.val,(Finset.mem_filter.mp j.property).1,h.1⟩

theorem rejectedDirectVertices_spec {V C J : Type*} (G : SimpleGraph V)
    (Q : Finset J) (T : J → Finset V) (σ : V → C×Bool) (c : C)
    {v : V} (hv : v∈rejectedDirectVertices G Q T σ c) :
    (σ v).1=c ∧ ¬coinColourSurvives G σ v ∧ ∃ j∈Q,v∈T j := by
  classical
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
  have h := rejectedDirectVertex_spec G Q T σ c j
  exact ⟨h.2.1,h.2.2,j.val,(Finset.mem_filter.mp j.property).1,h.1⟩

theorem assignedDirectVertices_preserve {V C J : Type*}
    (Q : Finset J) (T : J → Finset V) (σ τ : V → C×Bool) (c : C)
    (he : ∀ v∈assignedDirectVertices Q T σ c,σ v=τ v) :
    assignedSetIndices Q T σ c⊆assignedSetIndices Q T τ c := by
  classical
  intro j hj
  let j' : assignedSetIndices Q T σ c := ⟨j,hj⟩
  let v := assignedDirectVertex Q T σ c j'
  have hv : v∈assignedDirectVertices Q T σ c :=
    Finset.mem_image.mpr ⟨j',by simp,rfl⟩
  have h := assignedDirectVertex_spec Q T σ c j'
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,v,h.1,
    (congrArg Prod.fst (he v hv)).symm.trans h.2⟩

theorem rejectedDirectVertices_preserve {V C J : Type*} (G : SimpleGraph V)
    (Q : Finset J) (T : J → Finset V) (σ τ : V → C×Bool) (c : C)
    (he : ∀ v∈rejectedDirectVertices G Q T σ c,σ v=τ v)
    (hbad : ∀ v∈rejectedDirectVertices G Q T σ c,¬coinColourSurvives G τ v) :
    rejectedSetIndices G Q T σ c⊆rejectedSetIndices G Q T τ c := by
  classical
  intro j hj
  let j' : rejectedSetIndices G Q T σ c := ⟨j,hj⟩
  let v := rejectedDirectVertex G Q T σ c j'
  have hv : v∈rejectedDirectVertices G Q T σ c :=
    Finset.mem_image.mpr ⟨j',by simp,rfl⟩
  have h := rejectedDirectVertex_spec G Q T σ c j'
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,v,h.1,
    (congrArg Prod.fst (he v hv)).symm.trans h.2.1,hbad v hv⟩

end Oberwolfach
