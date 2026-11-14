module

public import Oberwolfach.ReservedCapacitySufficient

@[expose] public section
/-! Transfer the real block surplus and component count to the exact natural
floor capacity used by the reserved-path construction. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem sum_floor_capacity_of_real_surplus
    {I : Type*} [Fintype I] (a : I → ℕ) (b n : ℕ) (loss : ℝ)
    (hb : 0 < b)
    (hcomponents : (Fintype.card I : ℝ) ≤ loss)
    (hsurplus : (n : ℝ) < ((∑ i, a i : ℕ) : ℝ) / b - loss) :
    n ≤ ∑ i, a i / b := by
  classical
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hsum : (n : ℝ) + Fintype.card I < ((∑ i, a i : ℕ) : ℝ) / b := by linarith
  have hmul : ((b : ℝ) * ((n + Fintype.card I : ℕ) : ℝ)) < ((∑ i, a i : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, mul_comm] using (lt_div_iff₀ hbR).mp hsum
  have hnat : b * (n + Fintype.card I) ≤ ∑ i, a i := by
    exact_mod_cast (le_of_lt hmul)
  exact sum_floor_capacity_of_slack a b n hb hnat
end Oberwolfach
