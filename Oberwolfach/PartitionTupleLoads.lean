module

public import Oberwolfach.PartitionCyclicMatrices

@[expose] public section

/-! Exact transport of positional loads and the ordinary-edge load bounds
from class coordinates to the original vertex type. A label outside its
prescribed class has load zero. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem partitionTuple_position_loads {V : Type*} [Fintype V] {ℓ k : ℕ} {d : Fin k → ℕ}
    (P : FixedPartition V k d) (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k)
    (m : ℕ) (hm : ∀ s, d (a s) = m)
    (w : (Fin (ℓ + 2) → Fin m × Fin m) → ℝ) (q : ℝ)
    (hw : ∀ i x, (∑ s, if (s i).1 = x then w s else 0) = q ∧
      (∑ s, if (s i).2 = x then w s else 0) = q)
    (i : Fin (ℓ + 2)) (v : V) :
    (∑ t, if (t i).1 = v then embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w t else 0) =
      (if P.1 v = a (Sum.inl i) then q else 0) ∧
    (∑ t, if (t i).2 = v then embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w t else 0) =
      (if P.1 v = a (Sum.inr i) then q else 0) := by
  let f (j) := partitionCellEmbedding P (a (Sum.inl j)) m (hm _)
  let g (j) := partitionCellEmbedding P (a (Sum.inr j)) m (hm _)
  constructor
  · by_cases hv : P.1 v = a (Sum.inl i)
    · obtain ⟨x,hx⟩ := (partitionCellEmbedding_range P (a (Sum.inl i)) m (hm _) v).mpr hv
      rw [if_pos hv, ← hx]
      exact (pairTuple_weight_positions f g w i x).1.trans (hw i x).1
    · rw [if_neg hv]
      exact pairTuple_weight_position_outside f g w i v
        ((partitionCellEmbedding_range P (a (Sum.inl i)) m (hm _) v).not.mpr hv)
  · by_cases hv : P.1 v = a (Sum.inr i)
    · obtain ⟨x,hx⟩ := (partitionCellEmbedding_range P (a (Sum.inr i)) m (hm _) v).mpr hv
      rw [if_pos hv, ← hx]
      exact (pairTuple_weight_positions f g w i x).2.trans (hw i x).2
    · rw [if_neg hv, embeddedWeight_incidence]
      apply Finset.sum_eq_zero
      intro s _
      apply if_neg
      intro hs
      apply hv
      rw [← hs]
      exact partitionCellEmbedding_colour P (a (Sum.inr i)) m (hm _) (s i).2

theorem partitionTuple_left_edge_bounds {V : Type*} [Fintype V] {ℓ k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Fin (ℓ + 2) → Equiv.Perm V)
    (P : FixedPartition V k d) (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k)
    (m : ℕ) (hm : ∀ s, d (a s) = m)
    (w : (Fin (ℓ + 2) → Fin m × Fin m) → ℝ) (p : ℝ)
    (hw : ∀ i x y, (1 - p) * partitionCyclicMatrices G σ P a m hm (Sum.inl i) x y ≤
      (∑ s, if s i = (x,y) then w s else 0) ∧
      (∑ s, if s i = (x,y) then w s else 0) ≤
        partitionCyclicMatrices G σ P a m hm (Sum.inl i) x y)
    (i : Fin (ℓ + 2)) (x y : V) :
    (1 - p) * (if P.1 x = a (Sum.inl i) ∧ P.1 y = a (Sum.inr i) ∧ G.Adj x y then (1 : ℝ) else 0) ≤
      (∑ t, if t i = (x,y) then embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w t else 0) ∧
    (∑ t, if t i = (x,y) then embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w t else 0) ≤
      (if P.1 x = a (Sum.inl i) ∧ P.1 y = a (Sum.inr i) ∧ G.Adj x y then (1 : ℝ) else 0) := by
  let f (j) := partitionCellEmbedding P (a (Sum.inl j)) m (hm _)
  let g (j) := partitionCellEmbedding P (a (Sum.inr j)) m (hm _)
  by_cases hx : P.1 x = a (Sum.inl i)
  · by_cases hy : P.1 y = a (Sum.inr i)
    · obtain ⟨u,hu⟩ := (partitionCellEmbedding_range P (a (Sum.inl i)) m (hm _) x).mpr hx
      obtain ⟨v,hv⟩ := (partitionCellEmbedding_range P (a (Sum.inr i)) m (hm _) y).mpr hy
      have he := pairTuple_weight_left_edge f g w i u v
      have hh := hw i u v
      simp only [partitionCyclicMatrices, partitionInterfaceMatrix, Equiv.refl_apply,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero, hu, hv] at hh
      have hload : (∑ t, if t i = (x,y) then embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w t else 0) =
          ∑ s, if s i = (u,v) then w s else 0 := by
        simp only [f, g, hu, hv] at he
        convert he using 1 <;> apply Finset.sum_congr rfl <;> intro t _ <;> split_ifs <;> rfl
      rw [hload]
      simpa only [hx, hy, true_and] using hh
    · have hz : (∑ t, if t i = (x,y) then embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w t else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        split_ifs with ht
        · apply embeddedWeight_not_in_range
          intro hrange
          have hc := (partitionCyclicTupleEmbedding_range P a m hm t).mp hrange i
          exact hy (by simpa only [ht] using hc.2)
        · rfl
      simp only [hz, hy, false_and, and_false, ite_false, mul_zero, le_refl, and_self]
  · have hz : (∑ t, if t i = (x,y) then embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w t else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      split_ifs with ht
      · apply embeddedWeight_not_in_range
        intro hrange
        have hc := (partitionCyclicTupleEmbedding_range P a m hm t).mp hrange i
        exact hx (by simpa only [ht] using hc.1)
      · rfl
    simp only [hz, hx, false_and, ite_false, mul_zero, le_refl, and_self]

theorem partitionTuple_cross_edge_bounds {V : Type*} [Fintype V] {ℓ k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Fin (ℓ + 2) → Equiv.Perm V)
    (P : FixedPartition V k d) (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k)
    (m : ℕ) (hm : ∀ s, d (a s) = m)
    (w : (Fin (ℓ + 2) → Fin m × Fin m) → ℝ) (p : ℝ)
    (hw : ∀ i x y, (1 - p) * partitionCyclicMatrices G σ P a m hm (Sum.inr i) x y ≤
      (∑ s, if ((s i).2,(s (finRotate (ℓ + 2) i)).1) = (x,y) then w s else 0) ∧
      (∑ s, if ((s i).2,(s (finRotate (ℓ + 2) i)).1) = (x,y) then w s else 0) ≤
        partitionCyclicMatrices G σ P a m hm (Sum.inr i) x y)
    (i : Fin (ℓ + 2)) (x y : V) :
    (1 - p) * (if P.1 x = a (Sum.inr i) ∧ P.1 y = a (Sum.inl (finRotate (ℓ + 2) i)) ∧
      G.Adj x (σ i y) then (1 : ℝ) else 0) ≤
      (∑ t, if ((t i).2,(t (finRotate (ℓ + 2) i)).1) = (x,y)
        then embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w t else 0) ∧
    (∑ t, if ((t i).2,(t (finRotate (ℓ + 2) i)).1) = (x,y)
      then embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w t else 0) ≤
      (if P.1 x = a (Sum.inr i) ∧ P.1 y = a (Sum.inl (finRotate (ℓ + 2) i)) ∧
        G.Adj x (σ i y) then (1 : ℝ) else 0) := by
  let f (j) := partitionCellEmbedding P (a (Sum.inl j)) m (hm _)
  let g (j) := partitionCellEmbedding P (a (Sum.inr j)) m (hm _)
  by_cases hx : P.1 x = a (Sum.inr i)
  · by_cases hy : P.1 y = a (Sum.inl (finRotate (ℓ + 2) i))
    · obtain ⟨u,hu⟩ := (partitionCellEmbedding_range P (a (Sum.inr i)) m (hm _) x).mpr hx
      obtain ⟨v,hv⟩ := (partitionCellEmbedding_range P (a (Sum.inl (finRotate (ℓ + 2) i))) m (hm _) y).mpr hy
      have he := pairTuple_weight_cross_edge f g w i (finRotate (ℓ + 2) i) u v
      have hh := hw i u v
      simp only [partitionCyclicMatrices, partitionInterfaceMatrix,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero, hu, hv] at hh
      have hload : (∑ t, if ((t i).2,(t (finRotate (ℓ + 2) i)).1) = (x,y)
          then embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w t else 0) =
          ∑ s, if ((s i).2,(s (finRotate (ℓ + 2) i)).1) = (u,v) then w s else 0 := by
        simp only [f, g, hu, hv] at he
        convert he using 1 <;> apply Finset.sum_congr rfl <;> intro t _ <;> split_ifs <;> rfl
      rw [hload]
      simpa only [hx, hy, true_and] using hh
    · have hz : (∑ t, if ((t i).2,(t (finRotate (ℓ + 2) i)).1) = (x,y)
          then embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w t else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        split_ifs with ht
        · apply embeddedWeight_not_in_range
          intro hrange
          have hc := ((partitionCyclicTupleEmbedding_range P a m hm t).mp hrange
            (finRotate (ℓ + 2) i)).1
          have he : (t (finRotate (ℓ + 2) i)).1 = y := congrArg Prod.snd ht
          exact hy (by simpa only [he] using hc)
        · rfl
      simp only [hz, hy, false_and, and_false, ite_false, mul_zero, le_refl, and_self]
  · have hz : (∑ t, if ((t i).2,(t (finRotate (ℓ + 2) i)).1) = (x,y)
        then embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w t else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      split_ifs with ht
      · apply embeddedWeight_not_in_range
        intro hrange
        have hc := ((partitionCyclicTupleEmbedding_range P a m hm t).mp hrange i).2
        have he : (t i).2 = x := congrArg Prod.fst ht
        exact hx (by simpa only [he] using hc)
      · rfl
    simp only [hz, hx, false_and, ite_false, mul_zero, le_refl, and_self]

theorem partitionTuple_weight_support_and_bounds {V : Type*} [Fintype V]
    {ℓ k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Fin (ℓ + 2) → Equiv.Perm V)
    (P : FixedPartition V k d) (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k)
    (m : ℕ) (hm : ∀ s, d (a s) = m)
    (w : (Fin (ℓ + 2) → Fin m × Fin m) → ℝ) (A B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ v, 0 ≤ w v)
    (hs : ∀ v, 0 < w v → CyclicMatrixTupleValid (partitionCyclicMatrices G σ P a m hm) v)
    (hlo : ∀ v, CyclicMatrixTupleValid (partitionCyclicMatrices G σ P a m hm) v → A ≤ w v)
    (hhi : ∀ v, w v ≤ B) :
    let W := embeddedWeight (partitionCyclicTupleEmbedding P a m hm) w
    (∀ t, 0 ≤ W t ∧ W t ≤ B) ∧
    (∀ t, 0 < W t → TwistedCyclicTupleValid G σ t ∧
      ∀ i, P.1 (t i).1 = a (Sum.inl i) ∧ P.1 (t i).2 = a (Sum.inr i)) ∧
    (∀ t, TwistedCyclicTupleValid G σ t →
      (∀ i, P.1 (t i).1 = a (Sum.inl i) ∧ P.1 (t i).2 = a (Sum.inr i)) → A ≤ W t) := by
  let e := partitionCyclicTupleEmbedding P a m hm
  refine ⟨fun t => ⟨embeddedWeight_nonneg e w hw t, embeddedWeight_bound e w B hB hhi t⟩, ?_, ?_⟩
  · intro t ht
    have hrange : t ∈ Set.range e := by
      by_contra hn
      have hz := embeddedWeight_not_in_range e w t hn
      linarith
    obtain ⟨v,rfl⟩ := hrange
    rw [embeddedWeight_apply] at ht
    exact ⟨(partitionCyclicMatrices_valid G σ P a m hm v).mp (hs v ht),
      (partitionCyclicTupleEmbedding_range P a m hm (e v)).mp ⟨v,rfl⟩⟩
  · intro t ht hplace
    obtain ⟨v,rfl⟩ := (partitionCyclicTupleEmbedding_range P a m hm t).mpr hplace
    rw [embeddedWeight_apply]
    exact hlo v ((partitionCyclicMatrices_valid G σ P a m hm v).mpr ht)

end Oberwolfach
