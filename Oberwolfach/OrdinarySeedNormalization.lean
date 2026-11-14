module

public import Oberwolfach.OrdinaryAdmissibleCycleLoads

@[expose] public section

/-! Algebraic bounds for the fixed full-host seed coefficients. The bounds
are independent of the interval separation parameter. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem ordinary_seed_coefficient_bounds (r : ℕ) (hr : 2≤r)
    (n m ω p pR pH c B a : ℝ)
    (hn : 0<n) (hm : 0<m) (hω : 0<ω) (hp : 0<p)
    (hmlo : ω*n≤m) (hmhi : m≤n)
    (hRlo : p≤pR) (hRhi : pR≤1) (hHlo : p≤pH) (hHhi : pH≤1)
    (hc : 0≤c) (hB : 0≤B)
    (ha : c/n^(r-2)≤a) (hb : a≤B/n^(r-2)) :
    c/n^(r-1)≤a/(m*pR^(r-1)*pH^r) ∧
    a/(m*pR^(r-1)*pH^r)≤(B/(ω*p^(2*r-1)))/n^(r-1) := by
  have hR : 0<pR := hp.trans_le hRlo
  have hH : 0<pH := hp.trans_le hHlo
  have ha0 : 0≤a := (by positivity : 0≤c/n^(r-2)).trans ha
  have hexp : r-1=(r-2)+1 := by omega
  have hpow : n^(r-1)=n*n^(r-2) := by rw [hexp,pow_succ']
  have hsum : r-1+r=2*r-1 := by omega
  have hprod : p^(2*r-1)=p^(r-1)*p^r := by rw [← hsum,pow_add]
  have hden : 0<m*pR^(r-1)*pH^r := by positivity
  have hlo : ω*n*p^(2*r-1)≤m*pR^(r-1)*pH^r := by
    rw [hprod]
    calc
      _ = (ω*n)*p^(r-1)*p^r := by ring
      _ ≤ m*pR^(r-1)*pH^r := mul_le_mul
        (mul_le_mul hmlo (pow_le_pow_left₀ hp.le hRlo _) (by positivity) hm.le)
        (pow_le_pow_left₀ hp.le hHlo _) (by positivity) (by positivity)
  have hhi : m*pR^(r-1)*pH^r≤n := by
    calc
      _ ≤ m*1*1 := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_one₀ hR.le hRhi) hm.le)
        (pow_le_one₀ hH.le hHhi) (by positivity) (by positivity)
      _ = m := by ring
      _ ≤ n := hmhi
  constructor
  · calc
      _ = (c/n^(r-2))/n := by rw [hpow];field_simp <;> ring
      _ ≤ a/n := div_le_div_of_nonneg_right ha hn.le
      _ ≤ a/(m*pR^(r-1)*pH^r) := div_le_div_of_nonneg_left ha0 hden hhi
  · calc
      _ ≤ (B/n^(r-2))/(m*pR^(r-1)*pH^r) := div_le_div_of_nonneg_right hb hden.le
      _ ≤ (B/n^(r-2))/(ω*n*p^(2*r-1)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlo
      _ = _ := by rw [hpow];field_simp <;> ring

theorem ordinary_seed_mean_spoke_error (n D deg ε K μ : ℝ)
    (hn : 0<n) (hD : n/2≤D) (hε : 0≤ε) (hK : 0≤K)
    (hdeg : |deg-D|≤ε*n) (hmean : |μ-deg/D|≤6*K/D) :
    |μ-1|≤2*ε+12*K/n := by
  have hD0 : 0<D := lt_of_lt_of_le (half_pos hn) hD
  have hdegree : |deg/D-1|≤2*ε := by
    calc
      _ = |deg-D|/D := by
        have hh : deg/D-1=(deg-D)/D := by field_simp
        rw [hh,abs_div,abs_of_pos hD0]
      _ ≤ (ε*n)/D := div_le_div_of_nonneg_right hdeg hD0.le
      _ ≤ (ε*n)/(n/2) := div_le_div_of_nonneg_left (by positivity) (half_pos hn) hD
      _ = _ := by field_simp <;> ring
  have hmean' : |μ-deg/D|≤12*K/n := by
    calc
      _ ≤ 6*K/D := hmean
      _ ≤ (6*K)/(n/2) := div_le_div_of_nonneg_left (by positivity) (half_pos hn) hD
      _ = _ := by ring
  calc
    _ ≤ |μ-deg/D|+|deg/D-1| := abs_sub_le _ _ _
    _ ≤ 12*K/n+2*ε := add_le_add hmean' hdegree
    _ = _ := by ring

end Oberwolfach
