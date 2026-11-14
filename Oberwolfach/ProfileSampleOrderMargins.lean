module

public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! The bounded sample size is chosen after the fixed additional-set
size and before the ambient order or any forbidden graph is supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem profile_sample_order_union_margin (c q N₀ : ℕ) (hc : 1 ≤ c)
    (κv κr : ℝ) (hκv : 0 < κv) (hκr : 0 < κr) :
    ∃ t : ℕ,N₀ ≤ t ∧ q ≤ t ∧ 4 ≤ t ∧
      (2*Real.exp (-κv*t))*(c*(t+q):ℕ)+
        (2*Real.exp (-κr*t))*((c*(t+q):ℕ):ℝ)^c ≤ 1/4 := by
  let κ := min κv κr
  have hκ : 0 < κ := lt_min hκv hκr
  let C := 4*((2:ℝ)*c)^c
  obtain ⟨N,hN⟩ := eventually_stretchedExp_le_inv_pow C (c:ℝ) (c:=κ) (p:=1) hκ (by norm_num) 1
  let t := max (max N₀ q) (max N 4)
  have ht₀ : N₀ ≤ t := (le_max_left _ _).trans (le_max_left _ _)
  have htq : q ≤ t := (le_max_right _ _).trans (le_max_left _ _)
  have htN : N ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  have ht4 : 4 ≤ t := (le_max_right _ _).trans (le_max_right _ _)
  have htR : (4:ℝ) ≤ t := by exact_mod_cast ht4
  have htpos : (0:ℝ) < t := by linarith
  have htqR : (q:ℝ) ≤ t := by exact_mod_cast htq
  have hcR : (1:ℝ) ≤ c := by exact_mod_cast hc
  let M := ((c*(t+q):ℕ):ℝ)
  have hM : 1 ≤ M := by dsimp [M];push_cast;nlinarith [show (0:ℝ) ≤ q by positivity]
  have hMt : M ≤ (2:ℝ)*c*t := by dsimp [M];push_cast;nlinarith
  have hMc : M ≤ M^c := by
    have hh : M^1 ≤ M^c := pow_le_pow_right₀ hM hc
    simpa only [pow_one] using hh
  have hv : Real.exp (-κv*t) ≤ Real.exp (-κ*t) := by
    apply Real.exp_le_exp.mpr
    have hh := min_le_left κv κr
    dsimp [κ]
    nlinarith
  have hr : Real.exp (-κr*t) ≤ Real.exp (-κ*t) := by
    apply Real.exp_le_exp.mpr
    have hh := min_le_right κv κr
    dsimp [κ]
    nlinarith
  have htail : C*(t:ℝ)^c*Real.exp (-κ*t) ≤ 1/t := by
    simpa only [Real.rpow_natCast,Real.rpow_one,pow_one] using hN t htN
  refine ⟨t,ht₀,htq,ht4,?_⟩
  change (2*Real.exp (-κv*t))*M+(2*Real.exp (-κr*t))*M^c ≤ _
  calc
    _ ≤ 4*Real.exp (-κ*t)*M^c := by
      have hv' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv (show (0:ℝ) ≤ 2 by norm_num)) (show 0 ≤ M by linarith)
      have hr' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (show (0:ℝ) ≤ 2 by norm_num)) (pow_nonneg (show 0 ≤ M by linarith) c)
      have hm' := mul_le_mul_of_nonneg_left hMc (show 0 ≤ 2*Real.exp (-κ*t) by positivity)
      linarith
    _ ≤ 4*Real.exp (-κ*t)*(((2:ℝ)*c*t)^c) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_trans (by norm_num) hM) hMt c) (by positivity)
    _ = C*(t:ℝ)^c*Real.exp (-κ*t) := by dsimp [C];rw [mul_pow];ring
    _ ≤ 1/t := htail
    _ ≤ 1/4 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) htR)

end Oberwolfach
