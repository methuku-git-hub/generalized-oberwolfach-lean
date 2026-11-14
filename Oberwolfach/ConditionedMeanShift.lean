module

public import Mathlib.Tactic

@[expose] public section

/-! The mean of an intersection count after prescribing the classes of
at most a vertices differs from its unconditioned mean by at most 2a. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem conditioned_cell_mean_shift {a N r e u q v : ℝ}
    (ha : 0 ≤ a) (hN : 0 < N)
    (hr : 0 ≤ r ∧ r ≤ a) (he : 0 ≤ e ∧ e ≤ N)
    (hu : 0 ≤ u ∧ u ≤ a) (hq : 0 ≤ q ∧ q ≤ a) (hv : 0 ≤ v ∧ v ≤ N) :
    |u + v * (e / N) - (q + v) * ((r + e) / (a + N))| ≤ 2 * a := by
  have hn := add_pos_of_nonneg_of_pos ha hN
  let p := (r + e) / (a + N)
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    constructor
    · exact div_nonneg (add_nonneg hr.1 he.1) hn.le
    · apply (div_le_one hn).mpr
      linarith [hr.2, he.2]
  have hroot : |u - q * p| ≤ a := by
    have hqp := mul_le_mul_of_nonneg_left hp.2 hq.1
    have hqp0 := mul_nonneg hq.1 hp.1
    exact abs_le.mpr ⟨by nlinarith [hu.1,hq.2], by nlinarith [hu.2]⟩
  have hnum : |a * e - N * r| ≤ a * N := by
    have hae := mul_le_mul_of_nonneg_left he.2 ha
    have hNr := mul_le_mul_of_nonneg_left hr.2 hN.le
    have hae0 := mul_nonneg ha he.1
    have hNr0 := mul_nonneg hN.le hr.1
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hdiff : e / N - p = (a * e - N * r) / (N * (a + N)) := by
    dsimp [p]
    field_simp
    ring
  have hrem : |v * (e / N - p)| ≤ a := by
    rw [abs_mul, abs_of_nonneg hv.1, hdiff, abs_div, abs_of_pos (mul_pos hN hn)]
    calc
      v * (|a * e - N * r| / (N * (a + N))) ≤
          v * ((a * N) / (N * (a + N))) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity)) hv.1
      _ = v * a / (a + N) := by field_simp
      _ ≤ a := (div_le_iff₀ hn).mpr (by nlinarith [mul_le_mul_of_nonneg_left hv.2 ha])
  calc
    _ = |(u - q * p) + v * (e / N - p)| := by congr 1; dsimp [p]; ring
    _ ≤ |u - q * p| + |v * (e / N - p)| := abs_add_le _ _
    _ ≤ 2 * a := by linarith

end Oberwolfach
