module

public import Oberwolfach.SubsetComplement
public import Mathlib.Data.Nat.Factorial.BigOperators

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem choose_ratio_le_power {r n k : ℕ} (hr : r ≤ n) (hk : k ≤ n) :
    (r.choose k : ℝ) / n.choose k ≤ ((r : ℝ) / n) ^ k := by
  by_cases hn : n = 0
  · subst n
    have : k = 0 := by omega
    subst k
    simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  calc
    _ = ((k.factorial : ℝ) * r.choose k) / ((k.factorial : ℝ) * n.choose k) := by
      rw [mul_div_mul_left _ _ hfac]
    _ = (r.descFactorial k : ℝ) / n.descFactorial k := by
      simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    _ = ∏ i ∈ Finset.range k, ((r - i : ℕ) : ℝ) / (n - i : ℕ) := by
      simp only [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]
    _ ≤ ∏ i ∈ Finset.range k, ((r : ℝ) / n) := by
      apply Finset.prod_le_prod₀
      · intro i _
        positivity
      · intro i hi
        have hin : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
        have hd : (0 : ℝ) < (n - i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hin
        by_cases hir : i ≤ r
        · rw [Nat.cast_sub hir, Nat.cast_sub hin.le]
          have hdiff : (0 : ℝ) < (n : ℝ) - i := by
            have : (i : ℝ) < n := by exact_mod_cast hin
            linarith
          apply (div_le_div_iff₀ hdiff hnpos).mpr
          have hri : (r : ℝ) ≤ n := by exact_mod_cast hr
          nlinarith [show (0 : ℝ) ≤ i by positivity]
        · have : r - i = 0 := Nat.sub_eq_zero_of_le (by omega)
          rw [this]
          simp only [Nat.cast_zero, zero_div]
          exact div_nonneg (by positivity) hnpos.le
    _ = _ := by simp [div_pow]

end Oberwolfach
