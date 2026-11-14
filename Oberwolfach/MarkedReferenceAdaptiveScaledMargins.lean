module

public import Oberwolfach.MarkedReferenceAdaptiveParameterSelection

@[expose] public section
/-! Convert dimensionless change budgets to the original ambient-domain
error scale, without replacing it by an adaptive subdomain size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem marked_reference_scale_neighbourhood_margins
    (r:ℕ) (kappa ζ eps₁ eps₂ n:ℝ) (hn:0≤n)
    (hR:kappa/4+(r+12:ℝ)*(ζ+ζ)≤min eps₁ eps₂)
    (hI:kappa/4+(r+12:ℝ)*ζ≤min eps₁ eps₂):
    (kappa/4)*n+(r+12:ℝ)*(ζ*n+ζ*n)≤min eps₁ eps₂*n ∧
    (kappa/4)*n+(r+12:ℝ)*(ζ*n)≤min eps₁ eps₂*n:=by
  constructor
  · calc
      (kappa/4)*n+(r+12:ℝ)*(ζ*n+ζ*n)=(kappa/4+(r+12:ℝ)*(ζ+ζ))*n:=by ring
      _≤min eps₁ eps₂*n:=mul_le_mul_of_nonneg_right hR hn
  · calc
      (kappa/4)*n+(r+12:ℝ)*(ζ*n)=(kappa/4+(r+12:ℝ)*ζ)*n:=by ring
      _≤min eps₁ eps₂*n:=mul_le_mul_of_nonneg_right hI hn

theorem marked_reference_weighted_change_coefficient_nonnegative
    (r:ℕ) (B pstar:ℝ) (hB:0≤B) (hpstar:0<pstar):
    0≤15*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1)):=by positivity
end Oberwolfach
