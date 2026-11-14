module

public import Oberwolfach.PartitionTupleLoads
public import Oberwolfach.NearRegularCyclicWeights

@[expose] public section

/-! All incidence equations for the same weighting on one good partition.
These data are obtained from random regularization and the proved positive
cyclic decomposition; they are not inputs to the main theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure PartitionTupleWeightConditions {V : Type*} [Fintype V] {ℓ k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Fin (ℓ + 2) → Equiv.Perm V) (P : FixedPartition V k d)
    (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k) (p q A B : ℝ)
    (w : (Fin (ℓ + 2) → V × V) → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ w t
  support : ∀ t, 0 < w t → TwistedCyclicTupleValid G σ t ∧
    ∀ i, P.1 (t i).1 = a (Sum.inl i) ∧ P.1 (t i).2 = a (Sum.inr i)
  lower : ∀ t, TwistedCyclicTupleValid G σ t →
    (∀ i, P.1 (t i).1 = a (Sum.inl i) ∧ P.1 (t i).2 = a (Sum.inr i)) → A ≤ w t
  upper : ∀ t, w t ≤ B
  left : ∀ i x y,
    (1-p) * (if P.1 x = a (Sum.inl i) ∧ P.1 y = a (Sum.inr i) ∧ G.Adj x y then 1 else 0) ≤
      (∑ t, if t i = (x,y) then w t else 0) ∧
    (∑ t, if t i = (x,y) then w t else 0) ≤
      (if P.1 x = a (Sum.inl i) ∧ P.1 y = a (Sum.inr i) ∧ G.Adj x y then 1 else 0)
  right : ∀ i x y,
    (1-p) * (if P.1 x = a (Sum.inr i) ∧ P.1 y = a (Sum.inl (finRotate (ℓ + 2) i)) ∧
      G.Adj x (σ i y) then 1 else 0) ≤
      (∑ t, if ((t i).2,(t (finRotate (ℓ + 2) i)).1) = (x,y) then w t else 0) ∧
    (∑ t, if ((t i).2,(t (finRotate (ℓ + 2) i)).1) = (x,y) then w t else 0) ≤
      (if P.1 x = a (Sum.inr i) ∧ P.1 y = a (Sum.inl (finRotate (ℓ + 2) i)) ∧
        G.Adj x (σ i y) then 1 else 0)
  positions : ∀ i v,
    (∑ t, if (t i).1 = v then w t else 0) = (if P.1 v = a (Sum.inl i) then q else 0) ∧
    (∑ t, if (t i).2 = v then w t else 0) = (if P.1 v = a (Sum.inr i) then q else 0)

theorem near_regular_partition_tuple_weights (β : ℝ) (hβ : 0 < β) :
    ∃ C η₀ : ℝ, 0 < C ∧ 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ m₀ : ℕ, ∀ (V : Type) [Fintype V] (ℓ k : ℕ) (d : Fin k → ℕ)
      (G : SimpleGraph V) (σ : Fin (ℓ + 2) → Equiv.Perm V) (P : FixedPartition V k d)
      (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k) (m : ℕ) (hm : ∀ s, d (a s) = m),
      0 < m → m₀ ≤ m → ∀ d₀ α : ℝ, 0 < α →
      (1/2+β) * m ≤ d₀ - η * m →
      (∀ s v, |(graphCellDegree G (Equiv.refl V) P v (a s) : ℝ) - d₀| ≤ η * m) →
      (∀ i v, |(graphCellDegree G (σ i) P v (a (Sum.inl (finRotate (ℓ + 2) i))) : ℝ) - d₀| ≤ η * m) →
      let q := ⌊d₀ - Real.sqrt η * m⌋₊
      ((ℓ + 2) + (2 * (ℓ + 2) - 1) * α) * m ≤ (2 * (ℓ + 2) - 1) * (q : ℝ) →
      ∃ w, PartitionTupleWeightConditions G σ P a (C * Real.sqrt η) q
        ((1 - 2 * (ℓ + 2) * (C * Real.sqrt η)) *
          (((ℓ + 2 : ℝ) * cyclicSectorLower ℓ α) / (m : ℝ) ^ (2 * ℓ + 2)))
        (((ℓ + 2 : ℝ) * cyclicSectorUpper ℓ α) / (m : ℝ) ^ (2 * ℓ + 2)) w := by
  obtain ⟨C,η₀,hC,hη₀,hall⟩ := near_regular_cyclic_matrix_weights β hβ
  refine ⟨C,η₀,hC,hη₀,?_⟩
  intro η hη hηsmall
  obtain ⟨m₀,hm₀⟩ := hall η hη hηsmall
  refine ⟨m₀,?_⟩
  intro V _ ℓ k d G σ P a m hm hmpos hmlarge d₀ α hα hmin hid hσ q hthreshold
  letI : NeZero m := ⟨by omega⟩
  let M := partitionCyclicMatrices G σ P a m hm
  obtain ⟨hl,hr⟩ := partitionCyclicMatrices_near_degrees G σ P a m hm d₀ η hid hσ
  have hb := partitionCyclicMatrices_binary G σ P a m hm
  have ht := hm₀ ℓ (Fin m) (by simpa using hmlarge) M hb d₀ α hα
    (by intro i x; simpa only [Fintype.card_fin] using hmin.trans (hl i x).1)
    (by intro i y; simpa only [Fintype.card_fin] using hmin.trans (hr i y).1)
    (by simpa only [Fintype.card_fin] using hl)
    (by simpa only [Fintype.card_fin] using hr)
    (by simpa only [Fintype.card_fin] using hthreshold)
  simp only [Fintype.card_fin] at ht
  obtain ⟨w,hwn,hws,hwl,hwr,hwp,hwu,hwb⟩ := ht
  let W := embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w
  have hB : 0 ≤ ((ℓ + 2 : ℝ) * cyclicSectorUpper ℓ α) / (m : ℝ) ^ (2 * ℓ + 2) := by
    exact le_trans (hwn (fun _ => (0,0))) (hwu _)
  obtain ⟨hbound,hsupport,hlower⟩ := partitionTuple_weight_support_and_bounds G σ P a m hm
    w _ _ hB hwn hws hwb hwu
  refine ⟨W,⟨fun t => (hbound t).1, hsupport, hlower, fun t => (hbound t).2, ?_, ?_, ?_⟩⟩
  · exact partitionTuple_left_edge_bounds G σ P a m hm w (C * Real.sqrt η) (by
      intro i x y
      convert hwl i x y using 2 <;> apply Finset.sum_congr rfl <;> intro v _ <;> split_ifs <;> rfl)
  · exact partitionTuple_cross_edge_bounds G σ P a m hm w (C * Real.sqrt η) (by
      intro i x y
      convert hwr i x y using 2 <;> apply Finset.sum_congr rfl <;> intro v _ <;> split_ifs <;> rfl)
  · exact partitionTuple_position_loads P a m hm w q (by
      intro i x
      convert hwp i x using 2 <;> apply Finset.sum_congr rfl <;> intro v _ <;> split_ifs <;> rfl)

end Oberwolfach
