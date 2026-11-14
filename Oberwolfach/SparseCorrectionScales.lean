module

public import Mathlib.Tactic

@[expose] public section

/-! Explicit, uniformly chosen margins for sparse ordinary correction. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach

theorem sparse_correction_numeric {r n : ℕ} {δ ω ξ η h : ℝ}
    (hr : 0<r) (hδ : 0<δ) (hδ1 : δ≤1) (hω : 0<ω) (hω1 : ω≤1)
    (hξ : 0<ξ) (hξh : ξ≤h/100) (hη : 0≤η) (hηsmall : η≤δ*ω*ξ/1000)
    (hn : 100*((r : ℝ)+2)≤δ*ω*ξ*n) :
    let base := Nat.floor (ξ*n)
    (r : ℝ)≤δ*base ∧ 1≤δ*ω*base ∧
    η*n+2≤2*ω*base ∧
    3/2+η*n≤δ*(ω*base-η*n/2) ∧
    (base : ℝ)+r+η*n/2≤h*n/2 ∧
    2*((base : ℝ)+r+1)+η*n≤4*ξ*n ∧
    (base : ℝ)+r+1≤2*ξ*n := by
  intro base
  have hn0 : (0 : ℝ)≤n := Nat.cast_nonneg n
  have hr1 : (1 : ℝ)≤r := by exact_mod_cast hr
  have ha : 0≤ξ*n := mul_nonneg hξ.le hn0
  have hbl : ξ*n-1≤(base : ℝ) := by
    have hh := Nat.lt_floor_add_one (ξ*n)
    change ξ*n<(base : ℝ)+1 at hh
    linarith
  have hbu : (base : ℝ)≤ξ*n := Nat.floor_le ha
  have hc0 : 0≤δ*ω := mul_nonneg hδ.le hω.le
  have hc1 : δ*ω≤1 := by nlinarith [mul_le_mul_of_nonneg_left hω1 hδ.le]
  have hpA : δ*ω*(ξ*n)≤ξ*n := by nlinarith [mul_le_mul_of_nonneg_right hc1 ha]
  have hpW : δ*ω*(ξ*n)≤ω*(ξ*n) := by
    have hh := mul_le_mul_of_nonneg_right hδ1 (mul_nonneg hω.le ha)
    nlinarith
  have he0 : 0≤η*n := mul_nonneg hη hn0
  have hesmall : η*n≤δ*ω*(ξ*n)/1000 := by
    have hh := mul_le_mul_of_nonneg_right hηsmall hn0
    nlinarith
  have hδbl : δ*(ξ*n)-δ≤δ*base := by nlinarith [mul_le_mul_of_nonneg_left hbl hδ.le]
  have hcbl : δ*ω*(ξ*n)-1≤δ*ω*base := by
    have hh := mul_le_mul_of_nonneg_left hbl hc0
    nlinarith
  have hωbl : ω*(ξ*n)-1≤ω*base := by
    have hh := mul_le_mul_of_nonneg_left hbl hω.le
    nlinarith
  have hpδ : δ*ω*(ξ*n)≤δ*(ξ*n) := by
    have hh := mul_le_mul_of_nonneg_left hω1 (mul_nonneg hδ.le ha)
    nlinarith
  have hδe : δ*(η*n)≤η*n := by nlinarith [mul_le_mul_of_nonneg_right hδ1 he0]
  have hcap : 2*(ξ*n)≤h*n/2 := by
    have hh := mul_le_mul_of_nonneg_right hξh hn0
    nlinarith
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

/-- The order threshold is chosen before the vertex classes, graphs,
imbalance function or forbidden edges. -/
theorem sparse_correction_order_threshold (r : ℕ) {δ ω ξ : ℝ}
    (hδ : 0<δ) (hω : 0<ω) (hξ : 0<ξ) :
    ∃ n₀ : ℕ,1≤n₀ ∧ ∀ n : ℕ,n₀≤n →
      100*((r : ℝ)+2)≤δ*ω*ξ*n := by
  obtain ⟨N,hN⟩ := exists_nat_ge (100*((r : ℝ)+2)/(δ*ω*ξ))
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro n hn
  have hh : (N : ℝ)≤n := by exact_mod_cast (le_max_left _ _).trans hn
  have hp : 0<δ*ω*ξ := by positivity
  have h := (div_le_iff₀ hp).mp (hN.trans hh)
  nlinarith

end Oberwolfach
