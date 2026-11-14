module

public import Oberwolfach.RealFlow
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

/-! The residual two-edge path weighting, including continuity at zero residual
degree. Division by zero is zero in Lean, exactly as in the manuscript's cases. -/
set_option autoImplicit false
open scoped BigOperators Topology
noncomputable section
namespace Oberwolfach

theorem divided_product_bounds {a b d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (had : a ≤ d) (hbd : b ≤ d) :
    0 ≤ a * b / d ∧ a * b / d ≤ a ∧ a * b / d ≤ b ∧ a * b / d ≤ d := by
  have hd : 0 ≤ d := ha.trans had
  by_cases hz : d = 0
  · simp only [hz, div_zero, le_refl, true_and]
    exact ⟨ha, hb, trivial⟩
  · have hd' : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
    have hl : a * b / d ≤ a := (div_le_iff₀ hd').mpr (mul_le_mul_of_nonneg_left hbd ha)
    have hr : a * b / d ≤ b :=
      (div_le_iff₀ hd').mpr (by nlinarith [mul_le_mul_of_nonneg_right had hb])
    exact ⟨div_nonneg (mul_nonneg ha hb) hd, hl, hr, hl.trans had⟩

theorem continuous_divided_product {T : Type*} [TopologicalSpace T]
    (a b d : T → ℝ) (ha : Continuous a) (hb : Continuous b) (hd : Continuous d)
    (ha0 : ∀ t, 0 ≤ a t) (hb0 : ∀ t, 0 ≤ b t)
    (had : ∀ t, a t ≤ d t) (hbd : ∀ t, b t ≤ d t) :
    Continuous (fun t => a t * b t / d t) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases hz : d t = 0
  · change Filter.Tendsto (fun s => a s * b s / d s) (𝓝 t) (𝓝 (a t * b t / d t))
    rw [hz, div_zero]
    apply squeeze_zero
      (fun s => (divided_product_bounds (ha0 s) (hb0 s) (had s) (hbd s)).1)
      (fun s => (divided_product_bounds (ha0 s) (hb0 s) (had s) (hbd s)).2.2.2)
    have ht : Filter.Tendsto d (𝓝 t) (𝓝 (d t)) := hd.continuousAt
    rwa [hz] at ht
  · exact (ha.continuousAt.mul hb.continuousAt).div hd.continuousAt hz

def residualPath {X Y Z : Type*} [Fintype X]
    (A : X → Y → ℝ) (B : Y → Z → ℝ) (x : X) (y : Y) (z : Z) : ℝ :=
  A x y * B y z / (∑ w, A w y)

theorem residualPath_bounds {X Y Z : Type*} [Fintype X] [Fintype Z]
    (A : X → Y → ℝ) (B : Y → Z → ℝ)
    (hA : ∀ x y, 0 ≤ A x y) (hB : ∀ y z, 0 ≤ B y z)
    (hbal : ∀ y, ∑ x, A x y = ∑ z, B y z)
    (x : X) (y : Y) (z : Z) :
    0 ≤ residualPath A B x y z ∧
      residualPath A B x y z ≤ A x y ∧
      residualPath A B x y z ≤ B y z ∧
      residualPath A B x y z ≤ ∑ w, A w y := by
  apply divided_product_bounds (hA x y) (hB y z)
  · exact Finset.single_le_sum (fun w _ => hA w y) (Finset.mem_univ x)
  · rw [hbal]
    exact Finset.single_le_sum (fun w _ => hB y w) (Finset.mem_univ z)

theorem residualPath_left_load {X Y Z : Type*} [Fintype X] [Fintype Z]
    (A : X → Y → ℝ) (B : Y → Z → ℝ)
    (hA : ∀ x y, 0 ≤ A x y)
    (hbal : ∀ y, ∑ x, A x y = ∑ z, B y z)
    (x : X) (y : Y) :
    (∑ z, residualPath A B x y z) = A x y := by
  unfold residualPath
  rw [← Finset.sum_div, ← Finset.mul_sum, ← hbal y]
  by_cases hz : (∑ w, A w y) = 0
  · have hle := Finset.single_le_sum (s := Finset.univ)
      (fun w _ => hA w y) (Finset.mem_univ x)
    rw [hz] at hle
    have hx : A x y = 0 := le_antisymm hle (hA x y)
    simp only [hz, hx, mul_zero, zero_div]
  · exact mul_div_cancel_right₀ _ hz

theorem residualPath_right_load {X Y Z : Type*} [Fintype X] [Fintype Z]
    (A : X → Y → ℝ) (B : Y → Z → ℝ)
    (hB : ∀ y z, 0 ≤ B y z)
    (hbal : ∀ y, ∑ x, A x y = ∑ z, B y z)
    (y : Y) (z : Z) :
    (∑ x, residualPath A B x y z) = B y z := by
  unfold residualPath
  rw [← Finset.sum_div, ← Finset.sum_mul]
  by_cases hz : (∑ w, A w y) = 0
  · have hle := Finset.single_le_sum (s := Finset.univ)
      (fun w _ => hB y w) (Finset.mem_univ z)
    rw [← hbal y, hz] at hle
    have hz' : B y z = 0 := le_antisymm hle (hB y z)
    simp only [hz, hz', zero_mul, zero_div]
  · exact mul_div_cancel_left₀ _ hz

theorem residualPath_continuous {T X Y Z : Type*} [TopologicalSpace T]
    [Fintype X] [Fintype Y] [Fintype Z]
    (A : T → X → Y → ℝ) (B : T → Y → Z → ℝ)
    (hA : ∀ x y, Continuous (fun t => A t x y))
    (hB : ∀ y z, Continuous (fun t => B t y z))
    (hA0 : ∀ t x y, 0 ≤ A t x y) (hB0 : ∀ t y z, 0 ≤ B t y z)
    (hbal : ∀ t y, ∑ x, A t x y = ∑ z, B t y z) :
    Continuous (fun t x y z => residualPath (A t) (B t) x y z) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  apply continuous_pi
  intro z
  apply continuous_divided_product (fun t => A t x y) (fun t => B t y z)
    (fun t => ∑ w, A t w y) (hA x y) (hB y z) (by fun_prop)
    (fun t => hA0 t x y) (fun t => hB0 t y z)
  · intro t
    exact Finset.single_le_sum (fun w _ => hA0 t w y) (Finset.mem_univ x)
  · intro t
    rw [hbal t y]
    exact Finset.single_le_sum (fun w _ => hB0 t y w) (Finset.mem_univ z)

end Oberwolfach
