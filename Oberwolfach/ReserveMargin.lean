module

public import Oberwolfach.EndpointReserve

@[expose] public section

/-! Quantitative slack in the reserve capacities at a positive degree margin. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem reserve_capacity_positive_margin {k n δ d α : ℝ}
    (hk : 2 ≤ k) (hn : 0 < n) (hα : 0 < α)
    (hthreshold : (k + (2 * k - 1) * α) * n ≤ (2 * k - 1) * δ)
    (hd : δ ≤ d) (hdn : d ≤ n) (hδn : δ ≤ n) :
    let σ := (2 * k - 1) * α / k
    0 < σ ∧ σ < 1 ∧ 0 < d + δ - n ∧
      (d / k) / (d + δ - n) ≤ 1 - σ := by
  dsimp only
  have hk0 : 0 < k := by linarith
  have hfac : 0 < 2 * k - 1 := by linarith
  have hextra : 0 < (2 * k - 1) * α * n := mul_pos (mul_pos hfac hα) hn
  have hbase : k * n ≤ (2 * k - 1) * δ := by nlinarith
  have hδ0 : 0 ≤ δ :=
    (pos_of_mul_pos_right (lt_of_lt_of_le (mul_pos hk0 hn) hbase) hfac.le).le
  have hden := (reserve_capacity_inequality hk hn hδ0 hbase hd).1
  have hσ : 0 < (2 * k - 1) * α / k := div_pos (mul_pos hfac hα) hk0
  have hσk : (2 * k - 1) * α < k := by
    have hmul := mul_le_mul_of_nonneg_left hδn hfac.le
    nlinarith
  refine ⟨hσ, (div_lt_one hk0).mpr hσk, hden, ?_⟩
  apply (div_le_iff₀ hden).mpr
  apply (div_le_iff₀ hk0).mpr
  have hcalc : (1 - (2 * k - 1) * α / k) * (d + δ - n) * k =
      (k - (2 * k - 1) * α) * (d + δ - n) := by
    field_simp
  rw [hcalc]
  have hgap := mul_nonneg (by linarith : 0 ≤ k - 1) (sub_nonneg.mpr hd)
  have hdenle : d + δ - n ≤ n := by linarith
  have hslack := mul_le_mul_of_nonneg_left hdenle (mul_pos hfac hα).le
  nlinarith

theorem scaled_path_two_sided {a b d σ q n k : ℝ}
    (hσ : 0 < σ) (hq : 0 < q) (hn : 0 < n) (hk : 1 < k)
    (ha : σ ≤ a) (hb : σ ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hd : σ * q * n ≤ d) (hdn : d ≤ n) :
    σ ^ 2 / ((k - 1) * n) ≤ (a * b / d) / (k - 1) ∧
      (a * b / d) / (k - 1) ≤ 1 / ((k - 1) * σ * q * n) := by
  have hd0 : 0 < d := lt_of_lt_of_le (mul_pos (mul_pos hσ hq) hn) hd
  have hk1 : 0 < k - 1 := by linarith
  have ha0 : 0 ≤ a := (lt_of_lt_of_le hσ ha).le
  have hb0 : 0 ≤ b := (lt_of_lt_of_le hσ hb).le
  have hp : σ ^ 2 ≤ a * b := by nlinarith [mul_le_mul ha hb hσ.le ha0]
  have hp1 : a * b ≤ 1 := by nlinarith [mul_le_mul ha1 hb1 hb0 (by norm_num : (0 : ℝ) ≤ 1)]
  constructor
  · calc
      σ ^ 2 / ((k - 1) * n) = (σ ^ 2 / n) / (k - 1) := by field_simp
      _ ≤ (a * b / d) / (k - 1) := by
        apply div_le_div_of_nonneg_right _ hk1.le
        exact div_le_div₀ (mul_nonneg ha0 hb0) hp hd0 hdn
  · calc
      (a * b / d) / (k - 1) ≤ (1 / (σ * q * n)) / (k - 1) := by
        apply div_le_div_of_nonneg_right _ hk1.le
        exact div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1) hp1 (mul_pos (mul_pos hσ hq) hn) hd
      _ = 1 / ((k - 1) * σ * q * n) := by field_simp

end Oberwolfach
