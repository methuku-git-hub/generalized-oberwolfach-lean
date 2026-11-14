module

public import Oberwolfach.AbsorberFreeFamilies
public import Oberwolfach.FiniteImageCounts
public import Oberwolfach.ResourceTransformers

@[expose] public section

/-! Every compatible free configuration absorbs its prescribed root set.
The count is obtained from the actual map forgetting roots and the
second factor, with its bounded fibres. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype T] [DecidableEq T] {c : ℕ}

def compatibleFreeAbsorbers (R : C → Finset V) (S : T → VertexAbsorberTemplate c) (X : Finset V) :
    Finset (FreeAbsorberFamily R S) := Finset.univ.image (familyForgetAbsorberRoots R S X)

theorem compatible_free_absorber_count (R : C → Finset V) (S : T → VertexAbsorberTemplate c)
    (X : Finset V) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) :
    Fintype.card (LabelledAbsorberFamily R S X) ≤
      (compatibleFreeAbsorbers R S X).card*(Fintype.card T*X.card^c*J^(c+1)) := by
  exact finite_image_fibre_card_bound (familyForgetAbsorberRoots R S X) _
    (family_forget_absorber_roots_fibre_card R S X J hJ)

theorem compatible_free_absorber_absorbs (R : C → Finset V) (S : T → VertexAbsorberTemplate c)
    (X : Finset V) (F : FreeAbsorberFamily R S) (hF : F∈compatibleFreeAbsorbers R S X) :
    IsResourceAbsorber R X (freeAbsorberVertices R (S F.1) F.2) := by
  obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp hF
  have he : freeAbsorberVertices R (S D.1) (familyForgetAbsorberRoots R S X D).2=
      labelledAbsorberFree R (S D.1) X D.2 := rfl
  obtain ⟨hd,h₀,he₀,h₁,he₁⟩ := labelled_absorber_factors R (S D.1) X D.2
  refine ⟨?_,?_,?_⟩
  · exact hd
  · exact ⟨_,h₀,he₀⟩
  · exact ⟨_,h₁,he₁⟩

end Oberwolfach
