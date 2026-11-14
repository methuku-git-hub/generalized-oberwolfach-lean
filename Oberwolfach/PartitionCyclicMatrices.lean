module

public import Oberwolfach.PartitionInterfaceMatrices
public import Oberwolfach.PairTupleEmbedding
public import Oberwolfach.RegularCyclicMatrixWeights

@[expose] public section

/-! Cyclic interface matrices built from an actual partition and specified
permutations. The right interface uses the physical endpoint σᵢ(z).
The degree proof tests all vertices, including those outside a cell. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def partitionCyclicMatrices {V : Type*} [Fintype V] {ℓ k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Fin (ℓ + 2) → Equiv.Perm V)
    (P : FixedPartition V k d) (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k)
    (m : ℕ) (hm : ∀ s, d (a s) = m) :
    (Fin (ℓ + 2) ⊕ Fin (ℓ + 2)) → Fin m → Fin m → ℕ
  | Sum.inl i => partitionInterfaceMatrix G (Equiv.refl V) P
      (a (Sum.inl i)) (a (Sum.inr i)) m (hm _) (hm _)
  | Sum.inr i => partitionInterfaceMatrix G (σ i) P
      (a (Sum.inr i)) (a (Sum.inl (finRotate (ℓ + 2) i))) m (hm _) (hm _)

def partitionCyclicTupleEmbedding {V : Type*} [Fintype V] {ℓ k : ℕ} {d : Fin k → ℕ}
    (P : FixedPartition V k d) (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k)
    (m : ℕ) (hm : ∀ s, d (a s) = m) :
    (Fin (ℓ + 2) → Fin m × Fin m) ↪ (Fin (ℓ + 2) → V × V) :=
  pairTupleEmbedding
    (fun i => partitionCellEmbedding P (a (Sum.inl i)) m (hm _))
    (fun i => partitionCellEmbedding P (a (Sum.inr i)) m (hm _))

def TwistedCyclicTupleValid {V : Type*} {ℓ : ℕ} (G : SimpleGraph V)
    (σ : Fin (ℓ + 2) → Equiv.Perm V) (t : Fin (ℓ + 2) → V × V) : Prop :=
  ∀ i, G.Adj (t i).1 (t i).2 ∧ G.Adj (t i).2 (σ i (t (finRotate (ℓ + 2) i)).1)

theorem partitionCyclicMatrices_binary {V : Type*} [Fintype V] {ℓ k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Fin (ℓ + 2) → Equiv.Perm V)
    (P : FixedPartition V k d) (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k)
    (m : ℕ) (hm : ∀ s, d (a s) = m) (s) (x y : Fin m) :
    partitionCyclicMatrices G σ P a m hm s x y ≤ 1 := by
  cases s <;> exact partitionInterfaceMatrix_binary _ _ _ _ _ _ _ _ _ _

theorem partitionCyclicMatrices_valid {V : Type*} [Fintype V] {ℓ k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Fin (ℓ + 2) → Equiv.Perm V)
    (P : FixedPartition V k d) (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k)
    (m : ℕ) (hm : ∀ s, d (a s) = m) (v : Fin (ℓ + 2) → Fin m × Fin m) :
    CyclicMatrixTupleValid (partitionCyclicMatrices G σ P a m hm) v ↔
      TwistedCyclicTupleValid G σ (partitionCyclicTupleEmbedding P a m hm v) := by
  simp only [CyclicMatrixTupleValid, partitionCyclicMatrices, partitionInterfaceMatrix,
    partitionCyclicTupleEmbedding, pairTupleEmbedding, Function.Embedding.coeFn_mk,
    Equiv.refl_apply, TwistedCyclicTupleValid]
  have hi (Q : Prop) [Decidable Q] : (0 < (if Q then 1 else 0 : ℕ)) ↔ Q := by
    by_cases hQ : Q <;> simp [hQ]
  simp only [hi]

theorem partitionCyclicTupleEmbedding_range {V : Type*} [Fintype V] {ℓ k : ℕ} {d : Fin k → ℕ}
    (P : FixedPartition V k d) (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k)
    (m : ℕ) (hm : ∀ s, d (a s) = m) (t : Fin (ℓ + 2) → V × V) :
    t ∈ Set.range (partitionCyclicTupleEmbedding P a m hm) ↔
      ∀ i, P.1 (t i).1 = a (Sum.inl i) ∧ P.1 (t i).2 = a (Sum.inr i) := by
  rw [partitionCyclicTupleEmbedding, pairTupleEmbedding_range]
  simp only [partitionCellEmbedding_range]

theorem partitionCyclicMatrices_near_degrees {V : Type*} [Fintype V]
    {ℓ k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Fin (ℓ + 2) → Equiv.Perm V)
    (P : FixedPartition V k d) (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k)
    (m : ℕ) (hm : ∀ s, d (a s) = m) (d₀ η : ℝ)
    (hid : ∀ s v, |(graphCellDegree G (Equiv.refl V) P v (a s) : ℝ) - d₀| ≤ η * m)
    (hσ : ∀ i v, |(graphCellDegree G (σ i) P v (a (Sum.inl (finRotate (ℓ + 2) i))) : ℝ) - d₀| ≤ η * m) :
    (∀ s x, d₀ - η * m ≤ ((∑ y, partitionCyclicMatrices G σ P a m hm s x y : ℕ) : ℝ) ∧
      ((∑ y, partitionCyclicMatrices G σ P a m hm s x y : ℕ) : ℝ) ≤ d₀ + η * m) ∧
    (∀ s y, d₀ - η * m ≤ ((∑ x, partitionCyclicMatrices G σ P a m hm s x y : ℕ) : ℝ) ∧
      ((∑ x, partitionCyclicMatrices G σ P a m hm s x y : ℕ) : ℝ) ≤ d₀ + η * m) := by
  constructor
  · intro s x
    cases s with
    | inl i =>
      simp only [partitionCyclicMatrices, partitionInterfaceMatrix_row]
      have h := abs_le.mp (hid (Sum.inr i) (partitionCellEmbedding P (a (Sum.inl i)) m (hm _) x))
      constructor <;> linarith
    | inr i =>
      simp only [partitionCyclicMatrices, partitionInterfaceMatrix_row]
      have h := abs_le.mp (hσ i (partitionCellEmbedding P (a (Sum.inr i)) m (hm _) x))
      constructor <;> linarith
  · intro s y
    cases s with
    | inl i =>
      simp only [partitionCyclicMatrices, partitionInterfaceMatrix_column, Equiv.refl_apply]
      have h := abs_le.mp (hid (Sum.inl i) (partitionCellEmbedding P (a (Sum.inr i)) m (hm _) y))
      constructor <;> linarith
    | inr i =>
      simp only [partitionCyclicMatrices, partitionInterfaceMatrix_column]
      have h := abs_le.mp (hid (Sum.inr i)
        (σ i (partitionCellEmbedding P (a (Sum.inl (finRotate (ℓ + 2) i))) m (hm _) y)))
      constructor <;> linarith

end Oberwolfach
