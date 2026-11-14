module

public import Oberwolfach.RegularizationArithmetic
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! Constants for regularization are chosen from the fixed degree margin;
the order threshold is chosen only after the error parameter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem regularization_constants (β : ℝ) (hβ : 0 < β) :
    ∃ δ h C η₀ : ℝ,
      0 < δ ∧ δ ≤ 1 / 8 ∧ 0 < h ∧ h ≤ β - δ ∧ 0 < C ∧ C = 4 / h ∧ 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ →
        0 < Real.sqrt η ∧ Real.sqrt η ≤ 1 / 4 ∧ Real.sqrt η ≤ δ / 8 ∧
          0 < C * Real.sqrt η ∧ C * Real.sqrt η ≤ 1 := by
  let δ := min (β / 4) (1 / 8)
  let h := min (β / 2) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ8 : δ ≤ 1 / 8 := min_le_right _ _
  have hh : 0 < h := lt_min (by positivity) (by norm_num)
  have hhβ : h ≤ β - δ := by
    have hδβ : δ ≤ β / 4 := min_le_left _ _
    have hhβ : h ≤ β / 2 := min_le_left _ _
    linarith
  let C := 4 / h
  have hC : 0 < C := div_pos (by norm_num) hh
  let η₀ := min ((δ / 8) ^ 2) ((1 / C) ^ 2)
  have hη₀ : 0 < η₀ := lt_min (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  refine ⟨δ, h, C, η₀, hδ, hδ8, hh, hhβ, hC, rfl, hη₀, ?_⟩
  intro η hη hsmall
  have hs := (Real.sqrt_pos.mpr hη)
  have hsd : Real.sqrt η < δ / 8 := (Real.sqrt_lt' (by positivity)).mpr
    (hsmall.trans_le (min_le_left _ _))
  have hsC : Real.sqrt η < 1 / C := (Real.sqrt_lt' (by positivity)).mpr
    (hsmall.trans_le (min_le_right _ _))
  refine ⟨hs, by linarith, hsd.le, mul_pos hC hs, ?_⟩
  have hh := (lt_div_iff₀ hC).mp hsC
  nlinarith

theorem regularization_order_threshold (η : ℝ) (hη : 0 < η) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → 0 < m ∧ 1 ≤ η * m := by
  refine ⟨⌈1 / η⌉₊ + 1, by omega, ?_⟩
  intro m hm
  have hmpos : 0 < m := by omega
  have hceil : (1 / η : ℝ) ≤ m :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈1 / η⌉₊ ≤ m by omega))
  exact ⟨hmpos, by nlinarith [(div_le_iff₀ hη).mp hceil]⟩

end Oberwolfach
