module

public import Oberwolfach.PermutationImages
public import Oberwolfach.SubsetCounts

@[expose] public section

/-! Exact joint placement probabilities for distinct prescribed labels in
distinct cells of a uniform partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def distinctCellEmbeddingEquiv {I V : Type*} [Fintype V] {k : ℕ}
    {d : Fin k → ℕ} (P : FixedPartition V k d) (a : I ↪ Fin k) :
    {f : I ↪ V // ∀ i, P.1 (f i) = a i} ≃ (∀ i, {v : V // P.1 v = a i}) where
  toFun f i := ⟨f.1 i, f.2 i⟩
  invFun f := ⟨⟨fun i => (f i).1, by
    intro i j h
    apply a.injective
    calc
      a i = P.1 (f i).1 := (f i).2.symm
      _ = P.1 (f j).1 := congrArg P.1 h
      _ = a j := (f j).2⟩, fun i => (f i).2⟩
  left_inv f := by apply Subtype.ext; ext i; rfl
  right_inv f := by funext i; rfl

theorem distinctCell_embedding_count {I V : Type*} [Fintype I] [Fintype V]
    {k : ℕ} {d : Fin k → ℕ} (P : FixedPartition V k d) (a : I ↪ Fin k) :
    Fintype.card {f : I ↪ V // ∀ i, P.1 (f i) = a i} = ∏ i, d (a i) := by
  rw [Fintype.card_congr (distinctCellEmbeddingEquiv P a), Fintype.card_pi]
  simp only [P.2]

theorem uniformEmbedding_cell_probability {I V : Type*} [Fintype I] [Fintype V]
    [Nonempty (I ↪ V)] {k : ℕ} {d : Fin k → ℕ}
    (P : FixedPartition V k d) (a : I ↪ Fin k) :
    (FiniteLaw.uniform (I ↪ V)).probability (fun f => ∀ i, P.1 (f i) = a i) =
      ((∏ i, d (a i) : ℕ) : ℝ) / (Fintype.card V).descFactorial (Fintype.card I) := by
  rw [finiteLaw_uniform_probability, Fintype.card_embedding_eq]
  congr 1
  norm_cast
  convert! distinctCell_embedding_count P a using 1
  congr 1
  exact Subsingleton.elim _ _

theorem fixedPartition_joint_placement {I V : Type*} [Fintype I] [Fintype V]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)]
    (x : I ↪ V) (a : I ↪ Fin k) :
    (FiniteLaw.uniform (FixedPartition V k d)).probability
      (fun Q => ∀ i, Q.1 (x i) = a i) =
      ((∏ i, d (a i) : ℕ) : ℝ) / (Fintype.card V).descFactorial (Fintype.card I) := by
  letI : Nonempty (I ↪ V) := ⟨x⟩
  let P := Classical.choice (inferInstance : Nonempty (FixedPartition V k d))
  have h := uniformEmbedding_cell_probability P a
  rw [← uniformPermutation_inverse_images x, finiteLaw_map_probability] at h
  rw [← fixedPartition_uniform P, finiteLaw_map_probability]
  exact h

end Oberwolfach
