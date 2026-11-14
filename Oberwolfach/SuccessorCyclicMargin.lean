module

public import Oberwolfach.SuccessorDegreeScale
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! The original degree margin supplies both the random regularization
minimum degree and the cyclic fractional-decomposition threshold after
floor rounding. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def successorCycleRatio (k : ℕ) : ℝ := (k+2 : ℝ) / (2*(k+2)-1)

theorem successorCycleRatio_half_le (k : ℕ) : 1/2 ≤ successorCycleRatio k := by
  have hd : (0 : ℝ) < 2*(k+2)-1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  apply (le_div_iff₀ hd).mpr
  linarith

theorem successor_mean_lower {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (D q β ε : ℝ)
    (hmin : ∀ v, (q+β)*Fintype.card V ≤ (G.degree v : ℝ))
    (hnear : ∀ v, |(G.degree v : ℝ)-D| ≤ ε*Fintype.card V) :
    (q+β-ε)*Fintype.card V ≤ D := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have h := (abs_le.mp (hnear v)).2
  nlinarith [hmin v]

theorem successor_cyclic_numeric_inputs (k : ℕ) (n m D β ε η : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hβ : 0 < β)
    (hD : (successorCycleRatio k + β - ε)*n ≤ D)
    (hDhalf : n/2 ≤ D)
    (hη : ε+η ≤ β/4)
    (hsmall : Real.sqrt η ≤ 1/4)
    (hround : ε+Real.sqrt η+1/m ≤ β/2) :
    (1/2+β/4)*m ≤ D*(m/n)-η*m ∧
    0 ≤ D*(m/n)-Real.sqrt η*m ∧
    ((k+2)+(2*(k+2)-1)*(β/2))*m ≤
      (2*(k+2)-1)*(⌊D*(m/n)-Real.sqrt η*m⌋₊ : ℝ) := by
  have hden : (0 : ℝ) < 2*(k+2)-1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hd : (successorCycleRatio k+β-ε)*m ≤ D*(m/n) := by
    have hh := mul_le_mul_of_nonneg_right hD (div_nonneg hm.le hn.le)
    convert hh using 1 <;> field_simp
  have hhalf : m/2 ≤ D*(m/n) := by
    have hh := mul_le_mul_of_nonneg_right hDhalf (div_nonneg hm.le hn.le)
    convert hh using 1 <;> field_simp
  have hratio := successorCycleRatio_half_le k
  have hratioM := mul_le_mul_of_nonneg_right hratio hm.le
  have hηM := mul_le_mul_of_nonneg_right hη hm.le
  have hsM := mul_le_mul_of_nonneg_right hsmall hm.le
  refine ⟨by nlinarith,by nlinarith,?_⟩
  have hq := successor_regularized_degree_lower hn hm hD hround
  have ht := mul_le_mul_of_nonneg_left hq hden.le
  have he : (2*(k+2)-1) * successorCycleRatio k = (k+2 : ℝ) := by
    unfold successorCycleRatio
    field_simp
  have heq : ((k+2)+(2*(k+2)-1)*(β/2))*m =
      (2*(k+2)-1)*((successorCycleRatio k+β/2)*m) := by
    calc
      _ = ((2*(k+2)-1)*successorCycleRatio k + (2*(k+2)-1)*(β/2))*m := by rw [he]
      _ = _ := by ring
  rw [heq]
  simpa only [mul_div_assoc] using ht

end Oberwolfach
