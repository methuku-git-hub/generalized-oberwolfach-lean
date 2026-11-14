module

public import Oberwolfach.DirectedCutBounds

@[expose] public section

/-! The stronger cut coefficient required by the fixed numerical constants
of marked completion. The small-side and linear-side inequalities are
proved without changing the sampling law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem matrixCut_large_of_degree_and_quadratic_strong
    {V : Type*} [Fintype V] (G : SimpleGraph V) (M : V → V → ℕ)
    {α ρ δ t q : ℝ} (hα : 0 ≤ α) (hαmax : α ≤ 1 / 2) (hρ : 0 ≤ ρ)
    (hδa : δ ≤ α / 32) (hδr : δ ≤ ρ / 64)
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
    α * ρ / 4 * Fintype.card V * min (S.card : ℝ) T.card ≤ (matrixCut M S T : ℝ) := by
  let n : ℝ := Fintype.card V
  let s : ℝ := min (S.card : ℝ) T.card
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hs : 0 ≤ s := le_min (by positivity) (by positivity)
  by_cases hsmall : s ≤ ρ * n / 32
  · have hδn := mul_le_mul_of_nonneg_right hδr hn
    have hmargin : ρ * n / 8 ≤ ρ * n / 4 - t - ρ * n / 32 - 2 * δ * n := by
      change t ≤ ρ * n / 32 at ht
      nlinarith [mul_nonneg hρ hn]
    have hh := matrixCut_small_side M hM hrow hcol hmargin S T hlarge hsmall
    have hcoeff : α * ρ / 4 ≤ ρ / 8 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hn) hs
    dsimp [n, s] at hmul
    nlinarith
  · have hlin : ρ * n / 32 ≤ s := (lt_of_not_ge hsmall).le
    have hg := graphCut_large_of_minDegree G hdegree S T hlarge
    have hm := mul_le_mul_of_nonneg_left hg (div_nonneg hρ (by norm_num : (0 : ℝ) ≤ 2))
    have hc := (abs_lt.mp (hcut S T)).1
    have hqn := mul_le_mul_of_nonneg_right hq (sq_nonneg n)
    have hsn := mul_le_mul_of_nonneg_left hlin (show 0 ≤ α * ρ * n / 32 by positivity)
    have hδn := mul_le_mul_of_nonneg_right hδa (show 0 ≤ ρ / 2 * n * s by positivity)
    change (α - δ) * n * s ≤ (graphCut G S T : ℝ) at hg
    change ρ / 2 * ((α - δ) * n * s) ≤ ρ / 2 * (graphCut G S T : ℝ) at hm
    change -(q * n ^ 2) < (matrixCut M S T : ℝ) - ρ / 2 * graphCut G S T at hc
    change α * ρ / 4 * n * s ≤ (matrixCut M S T : ℝ)
    nlinarith [mul_nonneg hα (mul_nonneg hρ (mul_nonneg hn hs))]

end Oberwolfach
