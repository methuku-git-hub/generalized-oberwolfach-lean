module

public import Oberwolfach.LongReservedCapacityFromRoot

@[expose] public section
/-! The manuscript's n^(1/4) threshold and n^(3/4) demand error imply the
reserved-block floor capacity, under its displayed component and cutoff bounds. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_reserved_capacity_from_rpow
    {I : Type*} [Fintype I] (a : I → ℕ) (c d K demand : ℕ)
    (N ell theta : ℝ) (hc : 0 < c) (hd : 0 < d) (hK : 0 < K)
    (hN : 0 < N) (hθ : 0 < theta) (hell : (1:ℝ)/2 ≤ ell)
    (hmin : ∀ i, K ≤ a i)
    (htotal : ((∑ i, a i : ℕ) : ℝ) = ell*N)
    (hcut : 5/((c:ℝ)*(d:ℝ)+5) + (c:ℝ)*(d:ℝ)/K ≤ theta/2)
    (hlarge : 8*(c:ℝ)/theta < N^((1:ℝ)/4))
    (hdemand : (demand:ℝ) ≤ (1-theta)*ell*N/((c:ℝ)*(d:ℝ)) + 2*N^((3:ℝ)/4)/(d:ℝ)) :
    demand ≤ ∑ i, a i/(c*d+5) := by
  have h4 : (N^((1:ℝ)/4))^4 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN)]
    norm_num
  have h3 : (N^((1:ℝ)/4))^3 = N^((3:ℝ)/4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN)]
    norm_num
  have htotal' : ((∑ i, a i : ℕ) : ℝ) = ell*(N^((1:ℝ)/4))^4 := by
    simpa only [h4] using htotal
  have hdemand' : (demand:ℝ) ≤ (1-theta)*ell*(N^((1:ℝ)/4))^4/((c:ℝ)*(d:ℝ)) +
      2*(N^((1:ℝ)/4))^3/(d:ℝ) := by
    simpa only [h4,h3] using hdemand
  exact long_reserved_capacity_from_root a c d K demand (N^((1:ℝ)/4)) ell theta hc hd hK
    (Real.rpow_pos_of_pos hN _) hθ hell hmin htotal' hcut hlarge hdemand'
end Oberwolfach
