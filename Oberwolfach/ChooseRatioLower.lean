module

public import Oberwolfach.ChooseRatio
public import Mathlib.Algebra.Order.Ring.Pow

@[expose] public section

/-! Two-sided inclusion probabilities for sampling without replacement.
The relative error is explicit in the sample size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem choose_ratio_product {r n k : ℕ} :
    (r.choose k:ℝ)/n.choose k=
      ∏ i∈Finset.range k,((r-i:ℕ):ℝ)/(n-i:ℕ) := by
  have hf : (k.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  calc
    _ = ((k.factorial:ℝ)*r.choose k)/((k.factorial:ℝ)*n.choose k) := by rw [mul_div_mul_left _ _ hf]
    _ = (r.descFactorial k:ℝ)/n.descFactorial k := by
      simp only [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
    _ = _ := by simp only [Nat.descFactorial_eq_prod_range,Nat.cast_prod,Finset.prod_div_distrib]

theorem choose_ratio_lower_power {r n k : ℕ} (hr : r ≤ n) (hk : k ≤ r) (hn : 0 < n) :
    (((r-k:ℕ):ℝ)/n)^k ≤ (r.choose k:ℝ)/n.choose k := by
  rw [choose_ratio_product]
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  calc
    _ = ∏ _i∈Finset.range k,((r-k:ℕ):ℝ)/n := by simp [div_pow]
    _ ≤ _ := by
      apply Finset.prod_le_prod₀
      · intro i _;positivity
      · intro i hi
        have hik := Finset.mem_range.mp hi
        have hin : i < n := by omega
        have hd : (0:ℝ)<(n-i:ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hin
        have h₁ : ((r-k:ℕ):ℝ) ≤ (r-i:ℕ) := by exact_mod_cast (show r-k ≤ r-i by omega)
        have h₂ : ((n-i:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n i
        calc
          _ ≤ ((r-i:ℕ):ℝ)/n := div_le_div_of_nonneg_right h₁ hnp.le
          _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd h₂

theorem choose_ratio_relative_bounds {r n k : ℕ} (hr : r ≤ n) (hk : k ≤ r) (hr0 : 0 < r) :
    ((r:ℝ)/n)^k*(1-(k:ℝ)^2/r) ≤ (r.choose k:ℝ)/n.choose k ∧
      (r.choose k:ℝ)/n.choose k ≤ ((r:ℝ)/n)^k := by
  have hrp : (0:ℝ)<r := by exact_mod_cast hr0
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hkr : (k:ℝ)/r ≤ 1 := (div_le_one hrp).mpr (by exact_mod_cast hk)
  have hbern : 1-(k:ℝ)^2/r ≤ (1-(k:ℝ)/r)^k := by
    have hh := one_add_mul_le_pow (a:=-((k:ℝ)/r)) (by linarith : -2 ≤ -((k:ℝ)/r)) k
    convert hh using 1 <;> ring
  have he : ((r:ℝ)/n)^k*(1-(k:ℝ)/r)^k=(((r-k:ℕ):ℝ)/n)^k := by
    rw [← mul_pow,Nat.cast_sub hk]
    congr 1
    field_simp
  constructor
  · calc
      _ ≤ ((r:ℝ)/n)^k*(1-(k:ℝ)/r)^k := mul_le_mul_of_nonneg_left hbern (by positivity)
      _ = _ := he
      _ ≤ _ := choose_ratio_lower_power hr hk (by omega)
  · exact choose_ratio_le_power hr (hk.trans hr)

end Oberwolfach
