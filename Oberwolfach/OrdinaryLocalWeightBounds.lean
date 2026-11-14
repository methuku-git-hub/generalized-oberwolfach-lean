module

public import Mathlib.Tactic

@[expose] public section

/-! Explicit ambient-order bounds for the manuscript's fixed local cycle
coefficient 2 lambda/(D q^r s^(j(r-1))). -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach

theorem ordinary_local_denominator_bounds (m j : ℕ) (n D p q s : ℝ)
    (hn : 0<n) (hp : 0<p) (hp1 : p≤1) (hq : p≤q) (hq1 : q≤1) (hs : p≤s) (hs1 : s≤1)
    (hj : j≤2) (hD : n/2≤D) (hD' : D≤2*n) :
    n/2*p^(3*m+1)≤D*q^(m+1)*s^(j*m) ∧ D*q^(m+1)*s^(j*m)≤2*n := by
  have hq0 : 0<q := hp.trans_le hq
  have hs0 : 0<s := hp.trans_le hs
  have hD0 : 0<D := (half_pos hn).trans_le hD
  have hlow : p^(3*m+1)≤q^(m+1)*s^(j*m) := by
    calc
      _ = p^((m+1)+2*m) := by congr 1;omega
      _ = p^(m+1)*p^(2*m) := pow_add _ _ _
      _ ≤ p^(m+1)*p^(j*m) := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hp.le hp1 (Nat.mul_le_mul_right m hj)) (by positivity)
      _ ≤ _ := mul_le_mul (pow_le_pow_left₀ hp.le hq _) (pow_le_pow_left₀ hp.le hs _)
        (by positivity) (by positivity)
  have hhigh : q^(m+1)*s^(j*m)≤1 := by
    exact mul_le_one₀ (pow_le_one₀ hq0.le hq1) (by positivity) (pow_le_one₀ hs0.le hs1)
  constructor
  · have hh := mul_le_mul hD hlow (by positivity) hD0.le
    nlinarith only [hh]
  · have hh := mul_le_mul_of_nonneg_left hhigh hD0.le
    nlinarith only [hh,hD']

theorem ordinary_local_coefficient_bounds (m j : ℕ) (hm : 1≤m) (n D p q s b B weight : ℝ)
    (hn : 0<n) (hp : 0<p) (hp1 : p≤1) (hq : p≤q) (hq1 : q≤1) (hs : p≤s) (hs1 : s≤1)
    (hj : j≤2) (hD : n/2≤D) (hD' : D≤2*n) (hb : 0<b) (hB : 0≤B)
    (hweight : b/n^(m-1)≤weight ∧ weight≤B/n^(m-1)) :
    b/n^m≤2*weight/(D*q^(m+1)*s^(j*m)) ∧
      2*weight/(D*q^(m+1)*s^(j*m))≤(4*B/p^(3*m+1))/n^m := by
  have hq0 : 0<q := hp.trans_le hq
  have hs0 : 0<s := hp.trans_le hs
  have hD0 : 0<D := (half_pos hn).trans_le hD
  have hden := ordinary_local_denominator_bounds m j n D p q s hn hp hp1 hq hq1 hs hs1 hj hD hD'
  have hpow : n^m=n^(m-1)*n := by
    nth_rw 1 [← Nat.sub_add_cancel hm]
    exact pow_succ _ _
  have hweight0 : 0<weight := (div_pos hb (pow_pos hn _)).trans_le hweight.1
  constructor
  · apply le_trans _ (div_le_div_of_nonneg_left (by positivity : 0≤2*weight) (by positivity) hden.2)
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hweight.1 (by norm_num : (0:ℝ)≤2)) (by positivity : 0≤2*n)
    convert hh using 1 <;> rw [hpow] <;> field_simp <;> ring
  · apply (div_le_div_of_nonneg_left (by positivity : 0≤2*weight) (by positivity) hden.1).trans
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hweight.2 (by norm_num : (0:ℝ)≤2))
      (by positivity : 0≤n/2*p^(3*m+1))
    convert hh using 1 <;> rw [hpow] <;> field_simp <;> ring

end Oberwolfach
