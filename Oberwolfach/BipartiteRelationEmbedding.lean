module

public import Oberwolfach.BipartiteQuadraticCut
public import Oberwolfach.PartitionInterfaceMatrices

@[expose] public section

/-! Exact row, column and cut counts under injective labellings of a
bipartite part. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem embedding_predicate_card {I X : Type*} [Fintype I] [Fintype X]
    (f : I↪X) (P : X→Prop) :
    (Finset.univ.filter (fun i=>P (f i))).card≤(Finset.univ.filter P).card := by
  classical
  rw [← Finset.card_map f]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i,hi,rfl⟩:=Finset.mem_map.mp hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩

theorem bipartite_cut_embedding {I X Y : Type*} (f : I↪X)
    (M : X→Y→ℕ) (S : Finset I) (T : Finset Y) :
    bipartiteMatrixCut (fun i y=>M (f i) y) S T=bipartiteMatrixCut M (S.map f) T := by
  simp [bipartiteMatrixCut]

theorem partition_cell_predicate_card {X : Type*} [Fintype X] {m : ℕ}
    (P : FixedPartition X 2 (fun _=>m)) (i : Fin 2) (E : X→Prop) :
    (Finset.univ.filter (fun j : Fin m=>E (partitionCellEmbedding P i m rfl j))).card=
      ((Finset.univ.filter E)∩(fixedPartitionCell P i).val).card := by
  classical
  have hh:=partitionCellEmbedding_sum P i m rfl (fun x=>if E x then 1 else 0)
  have he : (Finset.univ.filter E)∩(fixedPartitionCell P i).val=Finset.univ.filter (fun x=>P.val x=i∧E x):=by
    ext x;simp [fixedPartitionCell,and_comm]
  rw [he]
  simpa only [Finset.card_filter,ite_and] using hh

end Oberwolfach
