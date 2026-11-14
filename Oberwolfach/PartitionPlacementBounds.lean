module

public import Oberwolfach.PartitionPlacement

@[expose] public section

/-! Exact two-label placement normalization and a lower bound uniform over
all choices of distinct labels in distinct equally sized cells. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def pairEmbedding {V : Type*} (x y : V) (h : x ≠ y) : Fin 2 ↪ V where
  toFun := ![x, y]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem fixedPartition_two_placement {V : Type*} [Fintype V]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)]
    (x y : V) (hxy : x ≠ y) (a b : Fin k) (hab : a ≠ b) :
    (FiniteLaw.uniform (FixedPartition V k d)).probability
      (fun P => P.1 x = a ∧ P.1 y = b) =
      ((d a : ℝ) * d b) / ((Fintype.card V : ℝ) * (Fintype.card V - 1)) := by
  have hn : 2 ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (pairEmbedding x y hxy).injective
  have h := fixedPartition_joint_placement (d := d) (pairEmbedding x y hxy) (pairEmbedding a b hab)
  simpa only [pairEmbedding, Function.Embedding.coeFn_mk, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two, Fintype.card_fin,
    Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one,
    Nat.cast_mul, Nat.cast_sub (show 1 ≤ Fintype.card V by omega), Nat.cast_one,
    mul_comm] using h

theorem fixedPartition_joint_placement_lower {I V : Type*} [Fintype I] [Fintype V]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)]
    (x : I ↪ V) (a : I ↪ Fin k) (m : ℕ) (hm : ∀ i, d (a i) = m)
    (hn : 0 < Fintype.card V) :
    ((m : ℝ) / Fintype.card V) ^ Fintype.card I ≤
      (FiniteLaw.uniform (FixedPartition V k d)).probability
        (fun P => ∀ i, P.1 (x i) = a i) := by
  rw [fixedPartition_joint_placement]
  simp only [hm, Finset.prod_const, Finset.card_univ, Nat.cast_pow, div_pow]
  have hinj : Fintype.card I ≤ Fintype.card V := Fintype.card_le_of_injective _ x.injective
  have hden : (0 : ℝ) < (Fintype.card V).descFactorial (Fintype.card I) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hinj
  have hpow : ((Fintype.card V).descFactorial (Fintype.card I) : ℝ) ≤
      (Fintype.card V : ℝ) ^ Fintype.card I := by
    exact_mod_cast Nat.descFactorial_le_pow (Fintype.card V) (Fintype.card I)
  exact div_le_div_of_nonneg_left (by positivity) hden hpow

end Oberwolfach
