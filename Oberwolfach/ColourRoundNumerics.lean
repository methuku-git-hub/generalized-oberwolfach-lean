module

public import Oberwolfach.SimplifiedCliqueJointRetention
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-! Numerical estimates used to iterate the checked colouring round. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Oberwolfach

theorem colouring_covariance_error_bound {l k s : ℕ} (hl : 1<l) (hs : s≤l) :
    let ρ := (1-1/(l : ℝ))^(k*s)
    1/(l : ℝ)+ρ*(2/(l : ℝ)+2*((k*s : ℕ) : ℝ)/((l : ℝ)*((l : ℝ)-1)))≤
      (3+4*(k : ℝ))/(l : ℝ) := by
  dsimp only
  have hlR : (2 : ℝ)≤l := by exact_mod_cast hl
  have hlpos : (0 : ℝ)<l := by linarith
  have hmpos : (0 : ℝ)<(l : ℝ)-1 := by linarith
  have hsR : (s : ℝ)≤l := by exact_mod_cast hs
  have hρ := equalized_retention_rate_bounds (by omega : 0<l) (k*s)
  have hterm : 2*((k*s : ℕ) : ℝ)/((l : ℝ)*((l : ℝ)-1))≤4*(k : ℝ)/(l : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hlpos hmpos) hlpos).mpr
    push_cast
    have hh := mul_nonneg (Nat.cast_nonneg k) (show 0≤2*((l : ℝ)-1)-(s : ℝ) by linarith)
    nlinarith [mul_nonneg hlpos.le hh]
  calc
    _ ≤ 1/(l : ℝ)+(2/(l : ℝ)+2*((k*s : ℕ) : ℝ)/((l : ℝ)*((l : ℝ)-1))) := by
      gcongr
      exact mul_le_of_le_one_left (by positivity) hρ.2
    _ ≤ 1/(l : ℝ)+(2/(l : ℝ)+4*(k : ℝ)/(l : ℝ)) := by linarith
    _ = _ := by ring

theorem colouring_retention_lower_bound {l k s : ℕ} (hl : 1<l) (hs : s≤l) :
    Real.exp (-2*(k : ℝ))≤(1-1/(l : ℝ))^(k*s) := by
  have hlR : (2 : ℝ)≤l := by exact_mod_cast hl
  have hlpos : (0 : ℝ)<l := by linarith
  have hmpos : (0 : ℝ)<(l : ℝ)-1 := by linarith
  have hsR : (s : ℝ)≤l := by exact_mod_cast hs
  have hx : 0<1-1/(l : ℝ) := by
    have hh : 1/(l : ℝ)<1 := (div_lt_one hlpos).mpr (by linarith)
    linarith
  have hinv : 1-(1-1/(l : ℝ))⁻¹= -1/((l : ℝ)-1) := by
    field_simp
    <;> ring
  have hi : 1/((l : ℝ)-1)≤2/(l : ℝ) := by
    apply (div_le_div_iff₀ hmpos hlpos).mpr
    linarith
  have hlog : -2/(l : ℝ)≤Real.log (1-1/(l : ℝ)) := by
    have hh := Real.one_sub_inv_le_log_of_pos hx
    rw [hinv,neg_div] at hh
    rw [neg_div]
    exact (neg_le_neg hi).trans hh
  rw [← Real.exp_log (pow_pos hx _),Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (k*s))
  have hb : -2*(k : ℝ)≤((k*s : ℕ) : ℝ)*(-2/(l : ℝ)) := by
    rw [Nat.cast_mul,← mul_div_assoc]
    apply (le_div_iff₀ hlpos).mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hsR)]
  exact hb.trans hh

theorem colouring_retention_upper_bound {l k s : ℕ} (hl : 1<l) :
    (1-1/(l : ℝ))^(k*s)≤Real.exp (-((k*s : ℕ) : ℝ)/(l : ℝ)) := by
  have hlpos : (0 : ℝ)<l := by exact_mod_cast (show 0<l by omega)
  have hlR : (1 : ℝ)<l := by exact_mod_cast hl
  have hx : 0<1-1/(l : ℝ) := by
    have hh : 1/(l : ℝ)<1 := (div_lt_one hlpos).mpr hlR
    linarith
  rw [← Real.exp_log (pow_pos hx _),Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) (Nat.cast_nonneg (k*s))
  convert hh using 1 <;> ring

theorem colouring_available_rate_bounds {l s : ℕ} (hl : 0<l) (hs : s≤l)
    {ρ : ℝ} (hρ : 0≤ρ ∧ ρ≤1) :
    1-ρ≤1-(s : ℝ)*ρ/(l : ℝ) ∧ 1-(s : ℝ)*ρ/(l : ℝ)≤1 := by
  have hlpos : (0 : ℝ)<l := Nat.cast_pos.mpr hl
  have hsR : (s : ℝ)≤l := by exact_mod_cast hs
  have hh : (s : ℝ)*ρ/(l : ℝ)≤ρ := by
    apply (div_le_iff₀ hlpos).mpr
    nlinarith [mul_nonneg hρ.1 (sub_nonneg.mpr hsR)]
  have hp : 0≤(s : ℝ)*ρ/(l : ℝ) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg s) hρ.1) hlpos.le
  exact ⟨by linarith,by linarith⟩

theorem colouring_comparison_gap {k : ℕ} (hk : 0<k) (l s ρ : ℝ) (hl : l≠0) :
    l*(1-s*ρ/l)^k-s*(1-ρ)*(1-s*ρ/l)^(k-1)=
      (l-s)*(1-s*ρ/l)^(k-1) := by
  rw [show (1-s*ρ/l)^k=(1-s*ρ/l)^(k-1)*(1-s*ρ/l) from by
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1≤k)]]
  have he : l*(1-s*ρ/l)=l-s*ρ := by field_simp
  calc
    _ = (l*(1-s*ρ/l)-s*(1-ρ))*(1-s*ρ/l)^(k-1) := by ring
    _ = _ := by rw [he];ring

end Oberwolfach
