module

public import Oberwolfach.PrescribedPositionsEmbeddingCombined

@[expose] public section
/-! A prescribed matching that avoids the reserved graph and an embedding
whose remaining edges avoid it together avoid the reserved graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem prescribed_edges_avoid_reserved (E M J:Finset (Sym2 V))
    (hM:Disjoint M J) (hnew:Disjoint (E\M) J):Disjoint E J := by
  apply Finset.disjoint_left.mpr
  intro e he hJ
  by_cases h:e∈M
  · exact (Finset.disjoint_left.mp hM h) hJ
  · exact (Finset.disjoint_left.mp hnew (Finset.mem_sdiff.mpr ⟨he,h⟩)) hJ
end Oberwolfach
