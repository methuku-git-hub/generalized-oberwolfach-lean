module

public import Oberwolfach.MarkedVortexNonDeeperGeometry
public import Oberwolfach.PermutationInvariantImage

@[expose] public section
/-! The parent, non-deeper and next-active permutations use the same
physical permutation, and the active image is invariant. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_nondeeper_permutation_embedding (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ)
    (x:markedVortexNonDeeperVertexType Q i):
    markedVortexNonDeeperVertexEmbedding Q i (markedVortexNonDeeperPermutation Q π hπ i x)=
      markedVortexPermutation Q π hπ i (markedVortexNonDeeperVertexEmbedding Q i x):=rfl

theorem marked_vortex_next_active_image_invariant (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ):
    ∀ x,markedVortexNonDeeperPermutation Q π hπ i x∈
      Finset.univ.image (markedVortexNextActiveInNonDeeper Q i) ↔
      x∈Finset.univ.image (markedVortexNextActiveInNonDeeper Q i):=by
  apply permutation_invariant_image (markedVortexNextActiveInNonDeeper Q i)
    (markedVortexNonDeeperPermutation Q π hπ i) (markedVortexActivePermutation Q π hπ (i+1))
    (marked_vortex_next_active_permutation_commutes Q π hπ i) Finset.univ
  intro x
  constructor <;> intro _ <;> exact Finset.mem_univ _
end Oberwolfach
