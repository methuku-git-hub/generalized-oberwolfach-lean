module

public import Oberwolfach.IntervalResidualMap
public import Oberwolfach.SectorBounds

@[expose] public section

/-! Bounds in the common part size for degree marginals and common neighbours. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem degree_marginal_scale {q n δ d : ℝ} (hq : 2 ≤ q) (hn : 0 < n)
    (ht : q * n ≤ (2 * q - 1) * δ) (hd : δ ≤ d) (hdn : d ≤ n) :
    (1 / (2 * q - 1)) * n ≤ d / q ∧ d / q ≤ (1 / q) * n := by
  have hq0 : 0 < q := by linarith
  have hf : 0 < 2 * q - 1 := by linarith
  constructor
  · rw [one_div_mul_eq_div, div_le_div_iff₀ hf hq0]
    nlinarith [mul_le_mul_of_nonneg_left hd hf.le]
  · rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hdn hq0.le

theorem intervalCommon_scale {X Y Z : Type*} [Fintype Y]
    (L : X → Y → Prop) (R : Y → Z → Prop) (q δ : ℝ)
    (hq : 2 ≤ q) (ht : q * Fintype.card Y ≤ (2 * q - 1) * δ)
    (hdL : ∀ x, δ ≤ (Finset.univ.filter (L x)).card)
    (hdR : ∀ z, δ ≤ (Finset.univ.filter (fun y => R y z)).card)
    (x : X) (z : Z) :
    (1 / (2 * q - 1)) * Fintype.card Y ≤ (intervalCommon L R x z : ℝ) ∧
    (intervalCommon L R x z : ℝ) ≤ (1 : ℝ) * Fintype.card Y := by
  have hf : 0 < 2 * q - 1 := by linarith
  have hc : ((Finset.univ.filter (L x)).card : ℝ) +
      (Finset.univ.filter (fun y => R y z)).card ≤
      (intervalCommon L R x z : ℝ) + Fintype.card Y := by
    exact_mod_cast intervalCommon_lower L R x z
  constructor
  · rw [one_div_mul_eq_div, div_le_iff₀ hf]
    have hd : 2 * δ ≤ (intervalCommon L R x z : ℝ) + Fintype.card Y := by
      linarith [hdL x, hdR z]
    nlinarith [mul_le_mul_of_nonneg_left hd hf.le]
  · rw [one_mul]
    exact_mod_cast Finset.card_le_univ (Finset.univ.filter (fun y => L x y ∧ R y z))

end Oberwolfach
