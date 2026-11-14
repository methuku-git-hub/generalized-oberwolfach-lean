module

public import Oberwolfach.SparseCorrectionScales

@[expose] public section

/-! Explicit scale inequalities for the four typed deletion matrices. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Oberwolfach

theorem typed_correction_numeric {n q : ℕ} {δ ω ξ η h : ℝ}
    (hq : 1≤q) (hδ : 0<δ) (hδ1 : δ≤1) (hω : 0<ω) (hω1 : ω≤1)
    (hξ : 0<ξ) (hξh : ((q:ℝ)+1)*ξ≤h/100) (hη : 0≤η)
    (hηsmall : η≤δ*ω*ξ/1000) (hn : 100≤δ*ω*ξ*n) :
    let base := Nat.floor (ξ*n)
    3+4*(η*n)≤δ*(ω*base-3*(η*n)) ∧
      (q:ℝ)*base+3*(η*n)≤h*n/2 ∧
      ((q:ℝ)+2)*base≤2*((q:ℝ)+1)*ξ*n := by
  intro base
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have hqR : (1:ℝ)≤q := by exact_mod_cast hq
  have ha : 0≤ξ*n := mul_nonneg hξ.le hn0
  have hbl : ξ*n-1≤(base:ℝ) := by
    have hh := Nat.lt_floor_add_one (ξ*n)
    change ξ*n<(base:ℝ)+1 at hh
    linarith
  have hbu : (base:ℝ)≤ξ*n := Nat.floor_le ha
  have hc0 : 0≤δ*ω := mul_nonneg hδ.le hω.le
  have hc1 : δ*ω≤1 := by nlinarith [mul_le_mul_of_nonneg_left hω1 hδ.le]
  have hCa : δ*ω*(ξ*n)≤ξ*n := by nlinarith [mul_le_mul_of_nonneg_right hc1 ha]
  have he0 : 0≤η*n := mul_nonneg hη hn0
  have hesmall : η*n≤δ*ω*(ξ*n)/1000 := by
    nlinarith [mul_le_mul_of_nonneg_right hηsmall hn0]
  have hcbl : δ*ω*(ξ*n)-1≤δ*ω*base := by
    nlinarith [mul_le_mul_of_nonneg_left hbl hc0]
  have hδe : δ*(η*n)≤η*n := by nlinarith [mul_le_mul_of_nonneg_right hδ1 he0]
  have hqb : (q:ℝ)*base≤q*(ξ*n) := mul_le_mul_of_nonneg_left hbu (Nat.cast_nonneg q)
  have hcap := mul_le_mul_of_nonneg_right hξh hn0
  have hq2b := mul_le_mul_of_nonneg_left hbu (show (0:ℝ)≤q+2 by positivity)
  have hqa := mul_nonneg (show (0:ℝ)≤q by positivity) ha
  refine ⟨?_,?_,?_⟩ <;> nlinarith

end Oberwolfach
