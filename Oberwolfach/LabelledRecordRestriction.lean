module

public import Oberwolfach.ResourceRestriction
public import Oberwolfach.AbsorberFreeCounts

@[expose] public section

/-! Restriction transports actual labelled realizations and all of
 their cycle identifiers. No new realizations or weights are supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W C O : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O] {h c : ℕ}

abbrev SupportedLabelledRecord (R : C → Finset V) (e : W ↪ V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset W) :=
  {D : LabelledCycleRecord R S (X.image e) // ∀ j,∃ w,e w=D.1.val j}

def restrictLabelledRecordMap (R : C → Finset V) (e : W ↪ V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset W)
    (D : SupportedLabelledRecord R e S X) : Fin h ⊕ Fin c → W :=
  fun j => Classical.choose (D.property j)

theorem restrictLabelledRecordMap_image (R : C → Finset V) (e : W ↪ V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset W)
    (D : SupportedLabelledRecord R e S X) (j : Fin h ⊕ Fin c) :
    e (restrictLabelledRecordMap R e S X D j)=D.val.1.val j :=
  Classical.choose_spec (D.property j)

def restrictLabelledRecord (R : C → Finset V) (e : W ↪ V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset W)
    (D : SupportedLabelledRecord R e S X) : LabelledCycleRecord (restrictedResourceSet R e) S X := by
  let g := restrictLabelledRecordMap R e S X D
  have hg (j) : e (g j)=D.val.1.val j := restrictLabelledRecordMap_image R e S X D j
  have hinj : Function.Injective g := by
    intro j k he
    apply D.val.1.property.1
    rw [← hg j,← hg k,he]
  have hroot : Finset.univ.image (fun i => g (Sum.inr i))=X := by
    apply Finset.image_injective e.injective
    rw [Finset.image_image]
    have he : e ∘ (fun i => g (Sum.inr i))=(fun i => D.val.1.val (Sum.inr i)) := by
      funext i;exact hg _
    rw [he,D.val.1.property.2]
  refine ⟨⟨g,hinj,hroot⟩,?_⟩
  intro o
  have hC : ∀ v∈R (D.val.2 o).val,∃ w,e w=v := by
    intro v hv
    rw [(D.val.2 o).property] at hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨g j,hg j⟩
  refine ⟨⟨(D.val.2 o).val,hC⟩,?_⟩
  apply Finset.image_injective e.injective
  rw [restrictedResourceSet_image,Finset.image_image]
  have he : e ∘ g=D.val.1.val := funext hg
  rw [he,(D.val.2 o).property]

theorem restrictLabelledRecord_map (R : C → Finset V) (e : W ↪ V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset W)
    (D : SupportedLabelledRecord R e S X) (j : Fin h ⊕ Fin c) :
    e ((restrictLabelledRecord R e S X D).1.val j)=D.val.1.val j :=
  restrictLabelledRecordMap_image R e S X D j

theorem restrictLabelledRecord_identifier (R : C → Finset V) (e : W ↪ V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset W)
    (D : SupportedLabelledRecord R e S X) (o : O) :
    ((restrictLabelledRecord R e S X D).2 o).val.val=(D.val.2 o).val := rfl

theorem restrictLabelledRecord_injective (R : C → Finset V) (e : W ↪ V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset W) :
    Function.Injective (restrictLabelledRecord R e S X) := by
  intro D E he
  apply Subtype.ext
  apply labelledCycleRecord_ext R S (X.image e) D.val E.val
  · intro j
    have hh := congrArg (fun D : LabelledCycleRecord (restrictedResourceSet R e) S X => e (D.1.val j)) he
    simpa only [restrictLabelledRecord_map] using hh
  · intro o
    have hh := congrArg (fun D : LabelledCycleRecord (restrictedResourceSet R e) S X => (D.2 o).val.val) he
    simpa only [restrictLabelledRecord_identifier] using hh

end Oberwolfach
