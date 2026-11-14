module

public import Oberwolfach.AbsorberFamilyRestriction
public import Oberwolfach.LabelledRecordDeletionCounts

@[expose] public section

/-! The lower bound for surviving labelled absorbers is obtained by
subtracting an explicit count, without changing the root or the templates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W C T : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T] {c : ℕ}

theorem restricted_absorber_card_loss (R : C → Finset V) (e : W ↪ V)
    (S : T → VertexAbsorberTemplate c) (X : Finset W) (Z : Finset V)
    (he : ∀ v,(∃ w,e w=v) ↔ v∉Z) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) :
    Fintype.card (LabelledAbsorberFamily R S (X.image e)) ≤
      Fintype.card (LabelledAbsorberFamily (restrictedResourceSet R e) S X)+
      Z.card*((c*c)*Fintype.card T*X.card^c*Fintype.card V^(c*c-1)*J^(2*c+1)) := by
  let D := LabelledAbsorberFamily R S (X.image e)
  let P (F : D) := Disjoint (labelledAbsorberFree R (S F.1) (X.image e) F.2) Z
  have hgood := restricted_absorber_avoiding_card R e S X Z he
  have hbad := labelled_absorber_free_deletion_count R S (X.image e) Z J hJ
  rw [Finset.card_image_of_injective _ e.injective] at hbad
  have hpart : Fintype.card {F : D // ¬P F}=Fintype.card D-Fintype.card {F : D // P F} :=
    Fintype.card_subtype_compl P
  have hle : Fintype.card {F : D // P F} ≤ Fintype.card D := Fintype.card_subtype_le P
  change Fintype.card {F : D // P F} ≤ _ at hgood
  change Fintype.card {F : D // ¬P F} ≤ _ at hbad
  change Fintype.card D ≤ _
  omega

end Oberwolfach
