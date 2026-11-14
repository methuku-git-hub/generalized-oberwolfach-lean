module

public import Oberwolfach.MarkedFixedVortexGeometry
public import Oberwolfach.PermutationEmbeddingWindows
public import Oberwolfach.OrdinaryRawIntervalGeometry

@[expose] public section
/-! Restricting a permutation to a vortex domain also restricts its entire
conflict graph, without adding a separate local forbidden-edge hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_fixed_vortex_conflict_restriction
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i b:ℕ):
    (permutationConflictGraph π b).comap (markedVortexVertexEmbedding Q i)=
      permutationConflictGraph (markedVortexPermutation Q π hπ i) b:=by
  let f:markedVortexVertexType Q i↪V:=(markedVortexVertexEmbedding Q i).toEmbedding
  let ρ:=markedVortexPermutation Q π hπ i
  have hcomm:∀x,f (ρ x)=π (f x):=(marked_vortex_permutation_compatibility Q π hπ i).1
  ext x y
  change (f x≠f y ∧ PermutationClose π b (f x) (f y)) ↔
    (x≠y ∧ PermutationClose ρ b x y)
  rw [f.injective.ne_iff,permutationClose_embedding f π ρ hcomm f.injective]
end Oberwolfach
