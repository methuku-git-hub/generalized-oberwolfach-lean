module

public import Oberwolfach.MatchingIntegerScales

@[expose] public section

/-! Integer partition scales satisfy all variance and codegree inequalities
used by the common-event argument. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach

theorem matching_power_scales (k h D n : ℕ) (hk : 2≤k) (hh : 2≤h)
    (hDn : n≤D) (hn : h^(64*k)≤n) (K : ℝ) (hK : 0<K) (hKh : 2*K≤h) :
    let p : ℝ := h^16
    let q := D/h^(16*k-12)
    h*p^(2*k)≤n ∧ h*p^k*q≤(D : ℝ)*n ∧
    (D : ℝ)^2*p*h≤4*(p^k)^2*q^2 ∧ (K*D/n)/(q : ℝ)≤1 := by
  dsimp only
  let m := h^(16*k-12)
  let q := D/m
  have hh0 : 0<h := by omega
  have hhR : (1 : ℝ)≤h := by exact_mod_cast (show 1≤h by omega)
  have hn0 : 0<n := lt_of_lt_of_le (pow_pos hh0 _) hn
  have hD0 : 0<D := hn0.trans_le hDn
  have hm0 : 0<m := pow_pos hh0 _
  have hmD : m≤D := by
    calc
      _ ≤ h^(64*k) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := hn
      _ ≤ D := hDn
  have hq0 : 0<q := Nat.div_pos hmD hm0
  have hfloor : D<m*q+m := by
    have hd := Nat.mod_lt D hm0
    have he := Nat.mod_add_div D m
    dsimp only [q]
    omega
  have hmq : (D : ℝ)≤2*(m : ℝ)*q := by
    have hd : (D : ℝ)<(m : ℝ)*q+m := by exact_mod_cast hfloor
    have hqR : (1 : ℝ)≤q := by exact_mod_cast hq0
    have hmR : (0 : ℝ)≤m := Nat.cast_nonneg m
    nlinarith
  have hnR : (h : ℝ)^(64*k)≤n := by exact_mod_cast hn
  have hbound (j : ℕ) (hj : j≤64*k) : (h : ℝ)^j≤n :=
    (pow_le_pow_right₀ hhR hj).trans hnR
  have hp2 : (h : ℝ)*((h : ℝ)^16)^(2*k)≤n := by
    rw [← pow_mul]
    have heq : (h : ℝ)*(h : ℝ)^(16*(2*k))=(h : ℝ)^(16*(2*k)+1) := by rw [pow_succ];ring
    rw [heq]
    exact hbound _ (by omega)
  have hp1 : (h : ℝ)*((h : ℝ)^16)^k≤n := by
    rw [← pow_mul]
    have heq : (h : ℝ)*(h : ℝ)^(16*k)=(h : ℝ)^(16*k+1) := by rw [pow_succ];ring
    rw [heq]
    exact hbound _ (by omega)
  have hqD : (q : ℝ)≤D := Nat.cast_le.mpr (Nat.div_le_self _ _)
  have hprod : (h : ℝ)*((h : ℝ)^16)^k*(q : ℝ)≤(D : ℝ)*n := by
    calc
      _ ≤ (n : ℝ)*q := mul_le_mul_of_nonneg_right hp1 (Nat.cast_nonneg _)
      _ ≤ (n : ℝ)*D := mul_le_mul_of_nonneg_left hqD (Nat.cast_nonneg _)
      _ = _ := by ring
  have hmP : (m : ℝ)^2*(h : ℝ)^16*h≤(((h : ℝ)^16)^k)^2 := by
    dsimp only [m]
    push_cast
    rw [← pow_mul,← pow_mul,← pow_mul,← pow_add]
    rw [← pow_succ]
    exact pow_le_pow_right₀ hhR (by omega)
  have hselection : (D : ℝ)^2*(h : ℝ)^16*h≤4*(((h : ℝ)^16)^k)^2*(q : ℝ)^2 := by
    have hsq : (D : ℝ)^2≤(2*(m : ℝ)*q)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmq 2
    have h1 := mul_le_mul_of_nonneg_right hsq (show 0≤(h : ℝ)^16*h by positivity)
    have h2 := mul_le_mul_of_nonneg_right hmP (show 0≤4*(q : ℝ)^2 by positivity)
    nlinarith
  have hcode : (K*D/n)/(q : ℝ)≤1 := by
    have hmn : (h : ℝ)*(m : ℝ)≤n := by
      dsimp only [m]
      push_cast
      have heq : (h : ℝ)*(h : ℝ)^(16*k-12)=(h : ℝ)^(16*k-12+1) := by rw [pow_succ];ring
      rw [heq]
      exact hbound _ (by omega)
    have hKm : 2*K*(m : ℝ)≤n := (mul_le_mul_of_nonneg_right hKh (Nat.cast_nonneg _)).trans hmn
    have h1 := mul_le_mul_of_nonneg_left hmq hK.le
    have h2 := mul_le_mul_of_nonneg_right hKm (Nat.cast_nonneg q)
    apply (div_le_iff₀ (Nat.cast_pos.mpr hq0)).mpr
    apply (div_le_iff₀ (Nat.cast_pos.mpr hn0)).mpr
    nlinarith
  exact ⟨hp2,hprod,hselection,hcode⟩

end Oberwolfach
