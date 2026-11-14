module

public import Oberwolfach.StochasticCyclicWeights
public import Oberwolfach.InterfaceFamilyRegularization
public import Oberwolfach.FiniteLawSupport

@[expose] public section

/-! Positive tuple weights for near-regular cyclic interfaces, obtained
from the proved random regularization theorem. No regularization or
fractional decomposition is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem near_regular_cyclic_matrix_weights (β : ℝ) (hβ : 0 < β) :
    ∃ C η₀ : ℝ, 0 < C ∧ 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ m₀ : ℕ, ∀ (k : ℕ) (X : Type) [Fintype X] [Nonempty X],
      m₀ ≤ Fintype.card X →
      ∀ (M : (Fin (k + 2) ⊕ Fin (k + 2)) → X → X → ℕ),
      (∀ i x y, M i x y ≤ 1) → ∀ d α : ℝ, 0 < α →
      (∀ i x, (1 / 2 + β) * Fintype.card X ≤ ((∑ y, M i x y : ℕ) : ℝ)) →
      (∀ i y, (1 / 2 + β) * Fintype.card X ≤ ((∑ x, M i x y : ℕ) : ℝ)) →
      (∀ i x, d - η * Fintype.card X ≤ ((∑ y, M i x y : ℕ) : ℝ) ∧
        ((∑ y, M i x y : ℕ) : ℝ) ≤ d + η * Fintype.card X) →
      (∀ i y, d - η * Fintype.card X ≤ ((∑ x, M i x y : ℕ) : ℝ) ∧
        ((∑ x, M i x y : ℕ) : ℝ) ≤ d + η * Fintype.card X) →
      let q := ⌊d - Real.sqrt η * Fintype.card X⌋₊
      ((k + 2) + (2 * (k + 2) - 1) * α) * Fintype.card X ≤
        (2 * (k + 2) - 1) * (q : ℝ) →
    ∃ w : (Fin (k + 2) → X × X) → ℝ,
      (∀ v, 0 ≤ w v) ∧
      (∀ v, 0 < w v → CyclicMatrixTupleValid M v) ∧
      (∀ i x y, (1 - C * Real.sqrt η) * M (Sum.inl i) x y ≤
        (∑ v, if v i = (x,y) then w v else 0) ∧
        (∑ v, if v i = (x,y) then w v else 0) ≤ M (Sum.inl i) x y) ∧
      (∀ i y z, (1 - C * Real.sqrt η) * M (Sum.inr i) y z ≤
        (∑ v, if ((v i).2, (v (finRotate (k + 2) i)).1) = (y,z) then w v else 0) ∧
        (∑ v, if ((v i).2, (v (finRotate (k + 2) i)).1) = (y,z) then w v else 0) ≤
          M (Sum.inr i) y z) ∧
      (∀ i x, (∑ v, if (v i).1 = x then w v else 0) = q ∧
        (∑ v, if (v i).2 = x then w v else 0) = q) ∧
      (∀ v, w v ≤ ((k + 2 : ℝ) * cyclicSectorUpper k α) /
        (Fintype.card X : ℝ) ^ (2 * k + 2)) ∧
      (∀ v, CyclicMatrixTupleValid M v →
        (1 - (2 * (k + 2 : ℝ)) * (C * Real.sqrt η)) *
          (((k + 2 : ℝ) * cyclicSectorLower k α) /
            (Fintype.card X : ℝ) ^ (2 * k + 2)) ≤ w v) := by
  obtain ⟨C, η₀, hC, hη₀, hall⟩ := interface_family_random_regularization β hβ
  refine ⟨C, η₀, hC, hη₀, ?_⟩
  intro η hη hηsmall
  obtain ⟨m₀, hm₀⟩ := hall η hη hηsmall
  refine ⟨m₀, ?_⟩
  intro k X _ _ hm M hM d α hα hl hr hnl hnr q hthreshold
  obtain ⟨ν, hregular, hsub, hprob⟩ := hm₀ (Fin (k + 2) ⊕ Fin (k + 2)) X hm
    M hM d hl hr hnl hnr
  let R (D : {D : ∀ i, BipartiteEdges (M i) → Bool // 0 < ν.mass D})
      (i : Fin (k + 2) ⊕ Fin (k + 2)) := retainedBipartiteMatrix (M i) (D.1 i)
  apply stochastic_cyclic_weights ν.support M hM R
    (fun D i x y => hsub D.1 i x y) q
    (fun D i x => (hregular D.1 D.2 i).1 x)
    (fun D i y => (hregular D.1 D.2 i).2 y) (C * Real.sqrt η) α hα _ hthreshold
  intro i x y hxy
  let e : BipartiteEdges (M i) := ⟨x,y,⟨0,hxy⟩⟩
  have h := hprob i e
  dsimp only [R]
  rw [finiteLaw_support_probability ν (fun D => retainedBipartiteMatrix (M i) (D i) x y = 0)]
  simpa only [e] using h

end Oberwolfach
