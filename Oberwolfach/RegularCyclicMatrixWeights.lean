module

public import Oberwolfach.CanonicalTupleDegrees

@[expose] public section

/-! Application of positive cyclic fractional weights to regular zero-one
interface matrices. The assertions include exact loads at every class
vertex and at every ordered interface edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem binary_matrix_count {X : Type*} [Fintype X] (f : X → ℕ)
    (hf : ∀ x, f x ≤ 1) : (Finset.univ.filter (fun x => 0 < f x)).card = ∑ x, f x := by
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x _
  have hx := hf x
  split_ifs <;> omega

def CyclicMatrixTupleValid {k : ℕ} {X : Type*}
    (M : (Fin (k + 2) ⊕ Fin (k + 2)) → X → X → ℕ)
    (v : Fin (k + 2) → X × X) : Prop :=
  ∀ i, 0 < M (Sum.inl i) (v i).1 (v i).2 ∧
    0 < M (Sum.inr i) (v i).2 (v (finRotate (k + 2) i)).1

theorem regular_cyclic_matrix_weights {k : ℕ} {X : Type*}
    [Fintype X] [Nonempty X]
    (M : (Fin (k + 2) ⊕ Fin (k + 2)) → X → X → ℕ)
    (hM : ∀ i x y, M i x y ≤ 1) (q : ℕ)
    (hrow : ∀ i x, ∑ y, M i x y = q)
    (hcol : ∀ i y, ∑ x, M i x y = q)
    (α : ℝ) (hα : 0 < α)
    (hthreshold : ((k + 2) + (2 * (k + 2) - 1) * α) * Fintype.card X ≤
      (2 * (k + 2) - 1) * q) :
    ∃ w : (Fin (k + 2) → X × X) → ℝ,
      (∀ v, 0 ≤ w v) ∧
      (∀ v, 0 < w v → CyclicMatrixTupleValid M v) ∧
      (∀ i x y, (∑ v, if v i = (x,y) then w v else 0) = M (Sum.inl i) x y) ∧
      (∀ i y z, (∑ v, if ((v i).2, (v (finRotate (k + 2) i)).1) = (y,z)
        then w v else 0) = M (Sum.inr i) y z) ∧
      (∀ i x, (∑ v, if (v i).1 = x then w v else 0) = q ∧
        (∑ v, if (v i).2 = x then w v else 0) = q) ∧
      (∀ v, w v ≤ ((k + 2 : ℝ) * cyclicSectorUpper k α) /
        (Fintype.card X : ℝ) ^ (2 * k + 2)) ∧
      (∀ v, CyclicMatrixTupleValid M v →
        ((k + 2 : ℝ) * cyclicSectorLower k α) /
          (Fintype.card X : ℝ) ^ (2 * k + 2) ≤ w v) := by
  classical
  let L (i : Fin (k + 2)) (x y : X) := 0 < M (Sum.inl i) x y
  let R (i : Fin (k + 2)) (x y : X) := 0 < M (Sum.inr i) x y
  have hlrow (i) (x) : (Finset.univ.filter (L i x)).card = q :=
    (binary_matrix_count _ (hM (Sum.inl i) x)).trans (hrow _ _)
  have hlcol (i) (y) : (Finset.univ.filter (fun x => L i x y)).card = q :=
    (binary_matrix_count _ (fun x => hM (Sum.inl i) x y)).trans (hcol _ _)
  have hrrow (i) (x) : (Finset.univ.filter (R i x)).card = q :=
    (binary_matrix_count _ (hM (Sum.inr i) x)).trans (hrow _ _)
  have hrcol (i) (y) : (Finset.univ.filter (fun x => R i x y)).card = q :=
    (binary_matrix_count _ (fun x => hM (Sum.inr i) x y)).trans (hcol _ _)
  obtain ⟨w, hw, hs, hl, hr, hb, hlo⟩ := canonical_cyclic_tuple_weights
    L R q α Fintype.card_pos hα hthreshold
    (fun i x => by simpa only [L, Finset.filter_congr_decidable] using (show (q : ℝ) ≤ (Finset.univ.filter (L i x)).card by rw [hlrow]))
    (fun i y => by simpa only [L, Finset.filter_congr_decidable] using (show (q : ℝ) ≤ (Finset.univ.filter (fun x => L i x y)).card by rw [hlcol]))
    (fun i y => by simpa only [L, R, Finset.filter_congr_decidable] using (hlcol i y).trans (hrrow i y).symm)
    (fun i x => by simpa only [L, R, Finset.filter_congr_decidable] using (hrcol i x).trans (hlrow (finRotate (k + 2) i) x).symm)
  have hcap (i) (x y : X) :
      (if 0 < M i x y then (1 : ℝ) else 0) = M i x y := by
    have hh := hM i x y
    split_ifs with hp
    · have he : M i x y = 1 := by omega
      simp [he]
    · have he : M i x y = 0 := by omega
      simp [he]
  refine ⟨w, hw, hs, ?_, ?_, ?_, hb, hlo⟩
  · intro i x y
    rw [hl]
    convert hcap (Sum.inl i) x y using 1
    unfold interfaceCapacity L
    split_ifs <;> rfl
  · intro i y z
    rw [hr]
    convert hcap (Sum.inr i) y z using 1
    unfold interfaceCapacity R
    split_ifs <;> rfl
  · intro i x
    have h := canonical_cyclic_position_loads L w hl i x
    simp only [L, Finset.filter_congr_decidable] at h
    simpa only [binary_matrix_count _ (hM (Sum.inl i) x), binary_matrix_count _ (fun y => hM (Sum.inl i) y x), hrow, hcol] using h

end Oberwolfach
