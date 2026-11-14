module

public import Oberwolfach.GraphPartitionDegrees

@[expose] public section

/-! Numbered vertices in a prescribed partition cell and the actual
ordinary or successor interface matrix. Row and column sums are exactly
the neighbourhood tests used by the conditional concentration theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def partitionCellEquiv {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (P : FixedPartition V k d) (a : Fin k) (m : ℕ) (hm : d a = m) :
    Fin m ≃ {v : V // P.1 v = a} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin]
    convert ((P.2 a).trans hm).symm using 1
    )

def partitionCellEmbedding {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (P : FixedPartition V k d) (a : Fin k) (m : ℕ) (hm : d a = m) : Fin m ↪ V :=
  (partitionCellEquiv P a m hm).toEmbedding.trans (Function.Embedding.subtype _)

theorem partitionCellEmbedding_colour {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (P : FixedPartition V k d) (a : Fin k) (m : ℕ) (hm : d a = m) (x : Fin m) :
    P.1 (partitionCellEmbedding P a m hm x) = a :=
  (partitionCellEquiv P a m hm x).2

theorem partitionCellEmbedding_range {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (P : FixedPartition V k d) (a : Fin k) (m : ℕ) (hm : d a = m) (v : V) :
    v ∈ Set.range (partitionCellEmbedding P a m hm) ↔ P.1 v = a := by
  constructor
  · rintro ⟨x,rfl⟩
    exact partitionCellEmbedding_colour P a m hm x
  · intro hv
    refine ⟨(partitionCellEquiv P a m hm).symm ⟨v,hv⟩, ?_⟩
    exact congrArg Subtype.val ((partitionCellEquiv P a m hm).apply_symm_apply ⟨v,hv⟩)

theorem partitionCellEmbedding_sum {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (P : FixedPartition V k d) (a : Fin k) (m : ℕ) (hm : d a = m) (f : V → ℕ) :
    (∑ x : Fin m, f (partitionCellEmbedding P a m hm x)) =
      ∑ v, if P.1 v = a then f v else 0 := by
  apply Fintype.sum_of_injective (partitionCellEmbedding P a m hm)
    (partitionCellEmbedding P a m hm).injective
  · intro v hv
    have hn := (partitionCellEmbedding_range P a m hm v).not.mp hv
    simp only [hn, ite_false]
  · intro x
    simp only [partitionCellEmbedding_colour, ite_true]

def partitionInterfaceMatrix {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Equiv.Perm V) (P : FixedPartition V k d)
    (a b : Fin k) (m : ℕ) (ha : d a = m) (hb : d b = m) (x y : Fin m) : ℕ :=
  if G.Adj (partitionCellEmbedding P a m ha x) (σ (partitionCellEmbedding P b m hb y))
    then 1 else 0

theorem partitionInterfaceMatrix_binary {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Equiv.Perm V) (P : FixedPartition V k d)
    (a b : Fin k) (m : ℕ) (ha : d a = m) (hb : d b = m) (x y : Fin m) :
    partitionInterfaceMatrix G σ P a b m ha hb x y ≤ 1 := by
  unfold partitionInterfaceMatrix
  split_ifs <;> omega

theorem partitionInterfaceMatrix_row {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Equiv.Perm V) (P : FixedPartition V k d)
    (a b : Fin k) (m : ℕ) (ha : d a = m) (hb : d b = m) (x : Fin m) :
    (∑ y, partitionInterfaceMatrix G σ P a b m ha hb x y) =
      graphCellDegree G σ P (partitionCellEmbedding P a m ha x) b := by
  unfold partitionInterfaceMatrix
  rw [partitionCellEmbedding_sum P b m hb (fun v => if G.Adj (partitionCellEmbedding P a m ha x) (σ v) then 1 else 0)]
  unfold graphCellDegree
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp_all

theorem partitionInterfaceMatrix_column {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Equiv.Perm V) (P : FixedPartition V k d)
    (a b : Fin k) (m : ℕ) (ha : d a = m) (hb : d b = m) (y : Fin m) :
    (∑ x, partitionInterfaceMatrix G σ P a b m ha hb x y) =
      graphCellDegree G (Equiv.refl V) P (σ (partitionCellEmbedding P b m hb y)) a := by
  unfold partitionInterfaceMatrix
  rw [partitionCellEmbedding_sum P a m ha (fun v => if G.Adj v (σ (partitionCellEmbedding P b m hb y)) then 1 else 0)]
  unfold graphCellDegree
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Equiv.refl_apply, G.adj_comm v]
  split_ifs <;> simp_all

end Oberwolfach
