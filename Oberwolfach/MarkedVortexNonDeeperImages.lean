module

public import Oberwolfach.MarkedVortexNonDeeperGeometry
public import Oberwolfach.MarkedVortexNonDeeperInnerHubs

@[expose] public section
/-! The non-deeper types embed as exactly the complements of the deeper
vertex and hub sets in the parent types. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_nondeeper_parent_images (i:ℕ):
    (Finset.univ.image (markedVortexNonDeeperVertexEmbedding Q i))=
      Finset.univ\markedVortexDeeperVertices Q i ∧
    (Finset.univ.image (markedVortexNonDeeperHubToParent Q i))=
      Finset.univ\markedVortexDeeperHubs Q i:=by
  constructor
  · ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_sdiff]
    constructor
    · rintro ⟨y,rfl⟩
      exact (Finset.mem_sdiff.mp y.property).2
    · intro hx
      exact ⟨⟨x,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hx⟩⟩,rfl⟩
  · ext u
    simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_sdiff]
    constructor
    · rintro ⟨y,rfl⟩
      exact (Finset.mem_sdiff.mp y.property).2
    · intro hu
      exact ⟨⟨u,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hu⟩⟩,rfl⟩

theorem marked_vortex_deeper_parent_permutation_invariant
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i:ℕ):∀ x,markedVortexPermutation Q π hπ i x∈markedVortexDeeperVertices Q i ↔
      x∈markedVortexDeeperVertices Q i:=
  (marked_vortex_permutation_compatibility Q π hπ i).2.2
end Oberwolfach
