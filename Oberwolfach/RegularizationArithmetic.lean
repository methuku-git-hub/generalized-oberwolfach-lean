module

public import Mathlib.Tactic

@[expose] public section

/-! Floor and scale estimates for regularizing a near-regular bipartite graph. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem regularization_floor_argument {n d η s β a : ℝ}
    (hn : 0 < n) (hβ : 0 ≤ β) (hs : 0 ≤ s) (hs4 : s ≤ 1 / 4)
    (hη : η = s ^ 2) (hamin : (1 / 2 + β) * n ≤ a) (haup : a ≤ d + η * n) :
    0 ≤ d - s * n := by
  have hη16 : η ≤ 1 / 16 := by nlinarith
  have hsm := mul_le_mul_of_nonneg_right hs4 hn.le
  have hηm := mul_le_mul_of_nonneg_right hη16 hn.le
  have hβm := mul_nonneg hβ hn.le
  nlinarith

theorem regularization_floor_demand {n d η s : ℝ} (a : ℕ)
    (hn : 0 < n) (harg : 0 ≤ d - s * n) (hηs : η ≤ s)
    (hnlarge : 1 ≤ η * n)
    (ha : d - η * n ≤ (a : ℝ) ∧ (a : ℝ) ≤ d + η * n) :
    let k := ⌊d - s * n⌋₊
    k ≤ a ∧ (s - η) * n ≤ ((a - k : ℕ) : ℝ) ∧
      ((a - k : ℕ) : ℝ) ≤ (s + 2 * η) * n := by
  dsimp only
  have hlo := Nat.floor_le harg
  have hhi := Nat.lt_floor_add_one (d - s * n)
  have hsn := mul_le_mul_of_nonneg_right hηs hn.le
  have hka : (⌊d - s * n⌋₊ : ℝ) ≤ a := by linarith [ha.1]
  have hka' : ⌊d - s * n⌋₊ ≤ a := by exact_mod_cast hka
  refine ⟨hka', ?_, ?_⟩ <;> rw [Nat.cast_sub hka'] <;> nlinarith [ha.1, ha.2]

theorem regularization_relative_scale {s η δ : ℝ}
    (hs : 0 < s) (hη : η = s ^ 2) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (hsmall : s ≤ δ / 8) :
    0 < s - η ∧ s + 2 * η ≤ (1 + δ) * (s - η) := by
  have hs1 : s < 1 := by linarith
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have hηs : η < s := by nlinarith
  have hδs := mul_le_mul_of_nonneg_right hsmall hs.le
  have hδη := mul_le_mul_of_nonneg_right hδ8 hη0
  constructor
  · exact sub_pos.mpr hηs
  · nlinarith

theorem regularization_capacity_scale {s η h C : ℝ}
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hη : η = s ^ 2)
    (hh : 0 < h) (hC : C = 4 / h) :
    s + 2 * η ≤ (C * s) * h / 2 := by
  have hcs : (C * s) * h / 2 = 2 * s := by rw [hC]; field_simp; ring
  rw [hcs]
  nlinarith

end Oberwolfach
