module

public import Oberwolfach.FixedPartitions

@[expose] public section

/-! Conditioning a fixed-size partition on the classes of fixed vertices.
Here X contains the fixed vertices and Y the remaining vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def rootCellSize {X : Type*} [Fintype X] {k : ℕ} (r : X → Fin k) (a : Fin k) : ℕ :=
  Fintype.card {x : X // r x = a}

abbrev RootedPartition (X Y : Type*) [Fintype X] [Fintype Y]
    (k : ℕ) (r : X → Fin k) (d : Fin k → ℕ) :=
  {P : FixedPartition (X ⊕ Y) k (fun a => rootCellSize r a + d a) //
    ∀ x, P.1 (Sum.inl x) = r x}

theorem sumColour_fibre_card {X Y C : Type*} [Fintype X] [Fintype Y] [DecidableEq C]
    (f : X ⊕ Y → C) (a : C) :
    Fintype.card {v : X ⊕ Y // f v = a} =
      Fintype.card {x : X // f (Sum.inl x) = a} +
      Fintype.card {y : Y // f (Sum.inr y) = a} := by
  simp only [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]

def rootPartitionExtend {X Y : Type*} [Fintype X] [Fintype Y]
    {k : ℕ} (r : X → Fin k) {d : Fin k → ℕ} (Q : FixedPartition Y k d) :
    RootedPartition X Y k r d :=
  ⟨⟨Sum.elim r Q.1, fun a => by
    rw [sumColour_fibre_card]
    exact congrArg (fun t => rootCellSize r a + t) (Q.2 a)⟩,
    fun _ => rfl⟩

def rootPartitionRestrict {X Y : Type*} [Fintype X] [Fintype Y]
    {k : ℕ} {r : X → Fin k} {d : Fin k → ℕ} (P : RootedPartition X Y k r d) :
    FixedPartition Y k d := by
  refine ⟨fun y => P.1.1 (Sum.inr y), ?_⟩
  intro a
  have h := P.1.2 a
  rw [sumColour_fibre_card] at h
  have hx : Fintype.card {x : X // P.1.1 (Sum.inl x) = a} = rootCellSize r a := by
    simp only [rootCellSize, P.2]
  rw [hx] at h
  exact Nat.add_left_cancel h

def rootedPartitionEquiv {X Y : Type*} [Fintype X] [Fintype Y]
    {k : ℕ} (r : X → Fin k) (d : Fin k → ℕ) :
    RootedPartition X Y k r d ≃ FixedPartition Y k d where
  toFun := rootPartitionRestrict
  invFun := rootPartitionExtend r
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    cases v with
    | inl x => exact (P.2 x).symm
    | inr y => rfl
  right_inv Q := by
    apply Subtype.ext
    rfl

theorem rootedPartition_uniform_restriction
    {X Y : Type*} [Fintype X] [Fintype Y]
    {k : ℕ} (r : X → Fin k) (d : Fin k → ℕ)
    [Nonempty (RootedPartition X Y k r d)] [Nonempty (FixedPartition Y k d)] :
    (FiniteLaw.uniform (RootedPartition X Y k r d)).map rootPartitionRestrict =
      FiniteLaw.uniform (FixedPartition Y k d) :=
  finiteLaw_uniform_map_equiv (rootedPartitionEquiv r d)

end Oberwolfach
