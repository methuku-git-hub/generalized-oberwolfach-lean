module

public import Oberwolfach.LongReservedCapacityFromCutoff
public import Oberwolfach.ReservedRootErrorBound

@[expose] public section
/-! Specialize the cutoff capacity to the paper's fourth-root error scale. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_reserved_capacity_from_root
    {I : Type*} [Fintype I] (a : I → ℕ) (c d K demand : ℕ)
    (x ell theta : ℝ) (hc : 0 < c) (hd : 0 < d) (hK : 0 < K)
    (hx : 0 < x) (hθ : 0 < theta) (hell : (1:ℝ)/2 ≤ ell)
    (hmin : ∀ i, K ≤ a i)
    (htotal : ((∑ i, a i : ℕ) : ℝ) = ell*x^4)
    (hcut : 5/((c:ℝ)*(d:ℝ)+5) + (c:ℝ)*(d:ℝ)/K ≤ theta/2)
    (hlarge : 8*(c:ℝ)/theta < x)
    (hdemand : (demand:ℝ) ≤ (1-theta)*ell*x^4/((c:ℝ)*(d:ℝ)) + 2*x^3/(d:ℝ)) :
    demand ≤ ∑ i, a i/(c*d+5) := by
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have herr := reserved_root_error_bound x c d theta hx hcR hdR hθ hlarge
  have hcut' : 5/((↑(c*d):ℝ)+5) + (↑(c*d):ℝ)/K ≤ theta/2 := by
    simpa only [Nat.cast_mul] using hcut
  have herr' : 2*x^3/(d:ℝ) < theta*x^4/(4*(↑(c*d):ℝ)) := by
    simpa only [Nat.cast_mul] using herr
  have hdemand' : (demand:ℝ) ≤ (1-theta)*ell*x^4/(↑(c*d):ℝ) + 2*x^3/(d:ℝ) := by
    simpa only [Nat.cast_mul] using hdemand
  exact long_reserved_capacity_from_cutoff a (c*d) K demand (x^4) ell theta (2*x^3/(d:ℝ))
    (Nat.mul_pos hc hd) hK (by positivity) hθ hell hmin htotal hcut' herr' hdemand'
end Oberwolfach
