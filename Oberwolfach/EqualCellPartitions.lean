module

public import Oberwolfach.FixedPartitions
public import Oberwolfach.PartitionPlacement

@[expose] public section

/-! Exactly c ordered cells of floor(n/c) vertices and one remainder cell.
The sample space includes the remainder; no vertex is discarded from the
probability space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def equalCellSizes (n c : ℕ) (a : Fin (c + 1)) : ℕ :=
  if a.val < c then n / c else n % c

theorem equalCellSizes_castSucc (n c : ℕ) (i : Fin c) :
    equalCellSizes n c i.castSucc = n / c := by simp [equalCellSizes, i.isLt]

theorem equalCellSizes_last (n c : ℕ) :
    equalCellSizes n c (Fin.last c) = n % c := by simp [equalCellSizes]

theorem equalCellSizes_sum (n c : ℕ) : ∑ a, equalCellSizes n c a = n := by
  rw [Fin.sum_univ_castSucc]
  simp only [equalCellSizes_castSucc, equalCellSizes_last, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h := Nat.mod_add_div n c
  omega

theorem equalCellPartition_nonempty {V : Type*} [Fintype V] (c : ℕ) :
    Nonempty (FixedPartition V (c + 1) (equalCellSizes (Fintype.card V) c)) :=
  fixedPartition_nonempty _ (equalCellSizes_sum _ _)

def equalCellAssignment (I : Type*) [Fintype I] : I ↪ Fin (Fintype.card I + 1) where
  toFun i := (Fintype.equivFin I i).castSucc
  inj' := by
    intro i j h
    exact (Fintype.equivFin I).injective (Fin.castSucc_injective _ h)

theorem equalCellAssignment_size (I : Type*) [Fintype I] (n : ℕ) (i : I) :
    equalCellSizes n (Fintype.card I) (equalCellAssignment I i) = n / Fintype.card I :=
  equalCellSizes_castSucc _ _ _

theorem fixedPartition_one_placement {V : Type*} [Fintype V]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)] (x : V) (a : Fin k) :
    (FiniteLaw.uniform (FixedPartition V k d)).probability (fun P => P.1 x = a) =
      (d a : ℝ) / Fintype.card V := by
  let e : Unit ↪ V := ⟨fun _ => x, fun i j _ => Subsingleton.elim i j⟩
  let f : Unit ↪ Fin k := ⟨fun _ => a, fun i j _ => Subsingleton.elim i j⟩
  have h := fixedPartition_joint_placement (d := d) e f
  simpa only [e, f, Function.Embedding.coeFn_mk, forall_const, Fintype.card_unit,
    Finset.prod_const, Finset.card_univ, pow_one, Nat.descFactorial_one] using h

end Oberwolfach
