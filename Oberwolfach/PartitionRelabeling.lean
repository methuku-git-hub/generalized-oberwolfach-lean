module

public import Oberwolfach.FixedPartitions
public import Mathlib.Logic.Equiv.Sum

@[expose] public section

/-! Relabelling prescribed-size partitions preserves their uniform law.
This connects fixed-root sum types to arbitrary subsets of the original
vertex domain without changing the sample space distribution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def fixedPartitionRelabel {V W : Type*} [Fintype V] [Fintype W]
    {k : ℕ} {d : Fin k → ℕ} (e : V ≃ W) (P : FixedPartition V k d) :
    FixedPartition W k d :=
  ⟨fun w => P.1 (e.symm w), fun a =>
    (Fintype.card_congr (e.symm.subtypeEquiv (fun _ => Iff.rfl))).trans (P.2 a)⟩

def fixedPartitionRelabelEquiv {V W : Type*} [Fintype V] [Fintype W]
    {k : ℕ} {d : Fin k → ℕ} (e : V ≃ W) :
    FixedPartition V k d ≃ FixedPartition W k d where
  toFun := fixedPartitionRelabel e
  invFun := fixedPartitionRelabel e.symm
  left_inv P := by apply Subtype.ext; funext x; simp [fixedPartitionRelabel]
  right_inv P := by apply Subtype.ext; funext x; simp [fixedPartitionRelabel]

theorem fixedPartition_relabel_uniform {V W : Type*} [Fintype V] [Fintype W]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)]
    [Nonempty (FixedPartition W k d)] (e : V ≃ W) :
    (FiniteLaw.uniform (FixedPartition V k d)).map (fixedPartitionRelabel e) =
      FiniteLaw.uniform (FixedPartition W k d) :=
  finiteLaw_uniform_map_equiv (fixedPartitionRelabelEquiv e)

theorem fixedPartition_root_decomposition {V : Type*} [Fintype V]
    {k : ℕ} {d : Fin k → ℕ} (R : Finset V) (P : FixedPartition V k d) :
    (∀ x : {x // x ∈ R},
      (fixedPartitionRelabel (Equiv.sumCompl (fun x => x ∈ R)).symm P).1 (Sum.inl x) = P.1 x) ∧
    (∀ y : {x // x ∉ R},
      (fixedPartitionRelabel (Equiv.sumCompl (fun x => x ∈ R)).symm P).1 (Sum.inr y) = P.1 y) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

end Oberwolfach
