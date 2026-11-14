module

public import Oberwolfach.StrongRawColourCutBounds

@[expose] public section

/-! The small-side and linear-side arguments for the initial directed
colour cuts, with the numerical inequalities stated explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem matrixCut_large_of_degree_and_quadratic
    {V : Type*} [Fintype V] (G : SimpleGraph V) (M : V → V → ℕ)
    {α ρ δ t q : ℝ} (hα : 0 ≤ α) (hαmax : α ≤ 1 / 2) (hρ : 0 ≤ ρ)
    (hδa : δ ≤ α / 32) (hδr : δ ≤ ρ / 512)
    (ht : t ≤ ρ * Fintype.card V / 32)
    (hq : q ≤ α * ρ ^ 2 / 1024)
    (hM : ∀ x y, M x y ≤ 1)
    (hdegree : ∀ x, (1 / 2 + α) * Fintype.card V ≤ (G.degree x : ℝ))
    (hrow : ∀ x, ρ * Fintype.card V / 4 - t ≤ ((∑ y, M x y : ℕ) : ℝ))
    (hcol : ∀ y, ρ * Fintype.card V / 4 - t ≤ ((∑ x, M x y : ℕ) : ℝ))
    (hcut : ∀ S T, |(matrixCut M S T : ℝ) - ρ / 2 * graphCut G S T| <
      q * (Fintype.card V : ℝ) ^ 2)
    (S T : Finset V)
    (hlarge : (1 - 2 * δ) * Fintype.card V < (S.card : ℝ) + T.card) :
    α * ρ / 64 * Fintype.card V * min (S.card : ℝ) T.card ≤ (matrixCut M S T : ℝ) := by
  have hh := matrixCut_large_of_degree_and_quadratic_strong G M hα hαmax hρ hδa
    (by linarith only [hδr,hρ]) ht hq hM hdegree hrow hcol hcut S T hlarge
  have hc : α*ρ/64≤α*ρ/4 := by nlinarith only [mul_nonneg hα hρ]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (Fintype.card V)))
    (show (0:ℝ)≤min (S.card:ℝ) T.card by positivity)).trans hh

end Oberwolfach
