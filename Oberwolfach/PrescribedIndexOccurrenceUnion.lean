module

public import Oberwolfach.PrescribedPositionsEmbeddingCombined

@[expose] public section
/-! For a fixed physical vertex, the indices at which it is prescribed in
one of three ways are contained in the union of the three index sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [DecidableEq I] [DecidableEq V]

theorem prescribed_union_occurrence_bound (P H Z:I→Finset V) (v:V):
    (Finset.univ.filter (fun i=>v∈P i∪H i∪Z i)).card≤
      (Finset.univ.filter (fun i=>v∈P i)).card+
      (Finset.univ.filter (fun i=>v∈H i)).card+
      (Finset.univ.filter (fun i=>v∈Z i)).card := by
  have hsets:(Finset.univ.filter (fun i=>v∈P i∪H i∪Z i))=
      (Finset.univ.filter (fun i=>v∈P i))∪(Finset.univ.filter (fun i=>v∈H i))∪
      (Finset.univ.filter (fun i=>v∈Z i)):=by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
  rw [hsets]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
end Oberwolfach
