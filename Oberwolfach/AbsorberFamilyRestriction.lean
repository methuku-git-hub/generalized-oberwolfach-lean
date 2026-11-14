module

public import Oberwolfach.LabelledRecordRestriction
public import Oberwolfach.AbsorberFreeFamilies

@[expose] public section

/-! The restriction map retains the template index, the complete label
map and every cycle identifier. Its injectivity preserves abundance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W C T : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T] {c : ℕ}

abbrev SupportedAbsorberFamily (R : C → Finset V) (e : W ↪ V)
    (S : T → VertexAbsorberTemplate c) (X : Finset W) :=
  {D : LabelledAbsorberFamily R S (X.image e) // ∀ j,∃ w,e w=D.2.1.val j}

def restrictAbsorberFamily (R : C → Finset V) (e : W ↪ V)
    (S : T → VertexAbsorberTemplate c) (X : Finset W)
    (D : SupportedAbsorberFamily R e S X) : LabelledAbsorberFamily (restrictedResourceSet R e) S X :=
  ⟨D.val.1,restrictLabelledRecord R e (S D.val.1).val X ⟨D.val.2,D.property⟩⟩

theorem restrictAbsorberFamily_injective (R : C → Finset V) (e : W ↪ V)
    (S : T → VertexAbsorberTemplate c) (X : Finset W) :
    Function.Injective (restrictAbsorberFamily R e S X) := by
  intro D E he
  apply Subtype.ext
  apply labelledAbsorberFamily_ext R S (X.image e) D.val E.val
  · exact congrArg (fun D : LabelledAbsorberFamily (restrictedResourceSet R e) S X => D.1) he
  · intro j
    have hh := congrArg (fun D : LabelledAbsorberFamily (restrictedResourceSet R e) S X => e (D.2.1.val j)) he
    simpa only [restrictAbsorberFamily,restrictLabelledRecord_map] using hh
  · intro o
    have hh := congrArg (fun D : LabelledAbsorberFamily (restrictedResourceSet R e) S X => (D.2.2 o).val.val) he
    simpa only [restrictAbsorberFamily,restrictLabelledRecord_identifier] using hh

theorem restricted_absorber_family_card (R : C → Finset V) (e : W ↪ V)
    (S : T → VertexAbsorberTemplate c) (X : Finset W) :
    Fintype.card (SupportedAbsorberFamily R e S X) ≤
      Fintype.card (LabelledAbsorberFamily (restrictedResourceSet R e) S X) :=
  Fintype.card_le_of_injective _ (restrictAbsorberFamily_injective R e S X)

theorem restricted_absorber_avoiding_card (R : C → Finset V) (e : W ↪ V)
    (S : T → VertexAbsorberTemplate c) (X : Finset W) (Z : Finset V)
    (he : ∀ v,(∃ w,e w=v) ↔ v∉Z) :
    Fintype.card {D : LabelledAbsorberFamily R S (X.image e) //
      Disjoint (labelledAbsorberFree R (S D.1) (X.image e) D.2) Z} ≤
      Fintype.card (LabelledAbsorberFamily (restrictedResourceSet R e) S X) := by
  let A := {D : LabelledAbsorberFamily R S (X.image e) //
    Disjoint (labelledAbsorberFree R (S D.1) (X.image e) D.2) Z}
  let f (D : A) : SupportedAbsorberFamily R e S X := ⟨D.val,by
    intro j
    rcases j with j | j
    · apply (he _).mpr
      intro hz
      exact Finset.disjoint_left.mp D.property (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩) hz
    · have hx := rootedLabelMap_root_mem (X.image e) D.val.2.1 j
      obtain ⟨w,hw,hw'⟩ := Finset.mem_image.mp hx
      exact ⟨w,hw'⟩⟩
  have hf : Function.Injective f := by
    intro D E hh;apply Subtype.ext;exact congrArg (fun D : SupportedAbsorberFamily R e S X => D.val) hh
  exact (Fintype.card_le_of_injective f hf).trans (restricted_absorber_family_card R e S X)

end Oberwolfach
