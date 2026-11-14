module

public import Oberwolfach.CyclicMatrixSurvival
public import Oberwolfach.AveragedDecompositions

@[expose] public section

/-! Average the positive fractional decompositions of regularized cyclic
interfaces. This is the regularization stage of the successor construction;
the outer random partition is handled separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem stochastic_cyclic_weights {Ω X : Type*} [Fintype Ω] [Fintype X] [Nonempty X]
    {k : ℕ} (μ : FiniteLaw Ω)
    (M : (Fin (k + 2) ⊕ Fin (k + 2)) → X → X → ℕ)
    (hM : ∀ i x y, M i x y ≤ 1)
    (R : Ω → (Fin (k + 2) ⊕ Fin (k + 2)) → X → X → ℕ)
    (hsub : ∀ ω i x y, R ω i x y ≤ M i x y)
    (q : ℕ) (hrow : ∀ ω i x, ∑ y, R ω i x y = q)
    (hcol : ∀ ω i y, ∑ x, R ω i x y = q)
    (p α : ℝ) (hα : 0 < α)
    (hprob : ∀ i x y, 0 < M i x y → μ.probability (fun ω => R ω i x y = 0) ≤ p)
    (hthreshold : ((k + 2) + (2 * (k + 2) - 1) * α) * Fintype.card X ≤
      (2 * (k + 2) - 1) * q) :
    ∃ w : (Fin (k + 2) → X × X) → ℝ,
      (∀ v, 0 ≤ w v) ∧
      (∀ v, 0 < w v → CyclicMatrixTupleValid M v) ∧
      (∀ i x y, (1 - p) * M (Sum.inl i) x y ≤
        (∑ v, if v i = (x,y) then w v else 0) ∧
        (∑ v, if v i = (x,y) then w v else 0) ≤ M (Sum.inl i) x y) ∧
      (∀ i y z, (1 - p) * M (Sum.inr i) y z ≤
        (∑ v, if ((v i).2, (v (finRotate (k + 2) i)).1) = (y,z) then w v else 0) ∧
        (∑ v, if ((v i).2, (v (finRotate (k + 2) i)).1) = (y,z) then w v else 0) ≤
          M (Sum.inr i) y z) ∧
      (∀ i x, (∑ v, if (v i).1 = x then w v else 0) = q ∧
        (∑ v, if (v i).2 = x then w v else 0) = q) ∧
      (∀ v, w v ≤ ((k + 2 : ℝ) * cyclicSectorUpper k α) /
        (Fintype.card X : ℝ) ^ (2 * k + 2)) ∧
      (∀ v, CyclicMatrixTupleValid M v →
        (1 - (2 * (k + 2 : ℝ)) * p) *
          (((k + 2 : ℝ) * cyclicSectorLower k α) /
            (Fintype.card X : ℝ) ^ (2 * k + 2)) ≤ w v) := by
  have hex (ω : Ω) := regular_cyclic_matrix_weights (R ω)
    (fun i x y => (hsub ω i x y).trans (hM i x y)) q (hrow ω) (hcol ω) α hα hthreshold
  choose W hW hs hl hr hv hb hlo using hex
  let w := averagedWeight μ W 1
  have hnonneg (v) : 0 ≤ w v := averagedWeight_nonneg μ W (by norm_num) hW v
  have hsupport (v) (hp : 0 < w v) : CyclicMatrixTupleValid M v := by
    by_contra hn
    have hz (ω) : W ω v = 0 := by
      by_contra hne
      have hvalid := hs ω v (lt_of_le_of_ne (hW ω v) (Ne.symm hne))
      apply hn
      intro i
      exact ⟨(hvalid i).1.trans_le (hsub ω _ _ _), (hvalid i).2.trans_le (hsub ω _ _ _)⟩
    have hzero : w v = 0 := by simp [w, averagedWeight, hz, finiteLaw_expectation_const]
    linarith
  refine ⟨w, hnonneg, hsupport, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x y
    have he := averagedWeight_incidence μ W 1 (fun v => v i = (x,y))
    simp only [div_one] at he
    have he' : (∑ v, if v i = (x,y) then w v else 0) =
        μ.expectation (fun ω => (R ω (Sum.inl i) x y : ℝ)) := by
      convert he using 1
      · apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> rfl
      · congr 1
        funext ω
        symm
        convert hl ω i x y using 1
        apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> rfl
    rw [he']
    exact finiteLaw_retained_binary_mean μ _ (hM _ _ _) _
      (fun ω => hsub ω _ _ _) p (hprob _ _ _)
  · intro i y z
    have he := averagedWeight_incidence μ W 1
      (fun v => ((v i).2, (v (finRotate (k + 2) i)).1) = (y,z))
    simp only [div_one] at he
    have he' : (∑ v, if ((v i).2, (v (finRotate (k + 2) i)).1) = (y,z) then w v else 0) =
        μ.expectation (fun ω => (R ω (Sum.inr i) y z : ℝ)) := by
      convert he using 1
      · apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> rfl
      · congr 1
        funext ω
        symm
        convert hr ω i y z using 1
        apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> rfl
    rw [he']
    exact finiteLaw_retained_binary_mean μ _ (hM _ _ _) _
      (fun ω => hsub ω _ _ _) p (hprob _ _ _)
  · intro i x
    constructor
    · have he := averagedWeight_incidence μ W 1 (fun v => (v i).1 = x)
      simpa only [fun ω => (hv ω i x).1, finiteLaw_expectation_const, div_one] using he
    · have he := averagedWeight_incidence μ W 1 (fun v => (v i).2 = x)
      simpa only [fun ω => (hv ω i x).2, finiteLaw_expectation_const, div_one] using he
  · intro v
    have h := (averagedWeight_pointwise_bounds μ W (by norm_num : (0 : ℝ) < 1)
      (fun ω v => CyclicMatrixTupleValid (R ω) v) hW hlo hb v).2
    simpa only [div_one] using h
  · intro v hvalid
    have h := (averagedWeight_pointwise_bounds μ W (by norm_num : (0 : ℝ) < 1)
      (fun ω v => CyclicMatrixTupleValid (R ω) v) hW hlo hb v).1
    simp only [div_one] at h
    have hsurvive := cyclicMatrix_tuple_survival μ M R p hprob v hvalid
    have ha : 0 ≤ ((k + 2 : ℝ) * cyclicSectorLower k α) /
        (Fintype.card X : ℝ) ^ (2 * k + 2) := by
      exact div_nonneg (mul_nonneg (by positivity) (cyclicSectorConstants_pos k α hα).1.le)
        (by positivity)
    exact (mul_le_mul_of_nonneg_right hsurvive ha).trans (by simpa only [mul_comm] using h)

end Oberwolfach
