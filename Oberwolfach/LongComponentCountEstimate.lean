module

public import Oberwolfach.ReservedCapacitySufficient

@[expose] public section
/-! Cycles of length at least K contribute at least K vertices each. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem component_count_le_total_div
    {I : Type*} [Fintype I] (a : I → ℕ) (K : ℕ) (hK : 0 < K)
    (hmin : ∀ i, K ≤ a i) :
    (Fintype.card I : ℝ) ≤ ((∑ i, a i : ℕ) : ℝ) / K := by
  classical
  have hnat : Fintype.card I * K ≤ ∑ i, a i := by
    calc
      Fintype.card I * K = ∑ _i : I, K := by simp
      _ ≤ ∑ i, a i := Finset.sum_le_sum (fun i _ => hmin i)
  apply (le_div_iff₀ (by exact_mod_cast hK : (0:ℝ)<K)).2
  exact_mod_cast hnat
end Oberwolfach
