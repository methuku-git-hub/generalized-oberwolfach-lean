module

public import Oberwolfach.ReservedCapacityFromReal
public import Oberwolfach.LongComponentCountEstimate
public import Oberwolfach.ReservedBlockCutoffArithmetic

@[expose] public section
/-! Discharge the reserved-block floor capacity from the long-component
count, the manuscript's cutoff, and its displayed raw-demand bound. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_reserved_capacity_from_cutoff
    {I : Type*} [Fintype I] (a : I → ℕ) (t K demand : ℕ)
    (N ell theta err : ℝ)
    (ht : 0 < t) (hK : 0 < K) (hN : 0 ≤ N) (hθ : 0 < theta)
    (hell : (1:ℝ)/2 ≤ ell) (hmin : ∀ i, K ≤ a i)
    (htotal : ((∑ i, a i : ℕ) : ℝ) = ell*N)
    (hcut : 5/((t:ℝ)+5) + (t:ℝ)/K ≤ theta/2)
    (herr : err < theta*N/(4*(t:ℝ)))
    (hdemand : (demand:ℝ) ≤ (1-theta)*ell*N/(t:ℝ) + err) :
    demand ≤ ∑ i, a i/(t+5) := by
  classical
  have htR : (0:ℝ) < t := by exact_mod_cast ht
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  have hcomponents := component_count_le_total_div a K hK hmin
  have hsur := reserved_block_surplus_of_cutoff N ell t K theta err
    hN htR hKR hθ hell hcut herr
  have hsurplus : (demand:ℝ) < ((∑ i, a i : ℕ) : ℝ)/(t+5:ℕ) -
      ((∑ i, a i : ℕ) : ℝ)/(K:ℝ) := by
    rw [htotal]
    push_cast
    exact lt_of_le_of_lt hdemand hsur
  exact sum_floor_capacity_of_real_surplus a (t+5) demand
    (((∑ i, a i : ℕ) : ℝ)/(K:ℝ)) (by omega) hcomponents hsurplus
end Oberwolfach
