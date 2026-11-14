module

public import Oberwolfach.OrdinaryFixedVortexConflict
public import Oberwolfach.PermutationConflictDegree

@[expose] public section
/-! The local permutation-conflict graph has the same uniform degree bound
as the ambient graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_fixed_vortex_conflict_degree
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i b:ℕ) (v:markedVortexVertexType Q i):
    ((permutationConflictGraph π b).comap (markedVortexVertexEmbedding Q i)).degree v≤2*b:=by
  let F:SimpleGraph (markedVortexVertexType Q i):=(permutationConflictGraph π b).comap (markedVortexVertexEmbedding Q i)
  have heq:F=permutationConflictGraph (markedVortexPermutation Q π hπ i) b:=
    ordinary_fixed_vortex_conflict_restriction P D m β ε Q π hπ i b
  have he:=congrArg (fun G:SimpleGraph (markedVortexVertexType Q i)=>G.neighborFinset v) heq
  have hc:=congrArg Finset.card he
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hh:=permutationConflictGraph_degree_le (markedVortexPermutation Q π hπ i) b v
  convert hc.le.trans hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
