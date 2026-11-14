module

public import Oberwolfach.MarkedTwoStageCommonTolerance

@[expose] public section
/-! The densities of the two-stage sample have a common positive lower
bound fixed from the original parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem marked_two_stage_density_lower_bounds
    (r:ℕ) (t rho:ℝ) (ht:0<t) (hrho:0<rho) (hrho1:rho≤1)
    (hst:(((r+1)+3:ℕ):ℝ)*t≤1):
    let pstar:=rho*t/2;
    0<pstar ∧ pstar≤1 ∧ pstar≤rho*((((r+1)+3:ℕ):ℝ)*t)/2 ∧
      pstar≤t ∧ pstar≤(((r+1)+3:ℕ):ℝ)*t:=by
  intro pstar
  have hr:(1:ℝ)≤(((r+1)+3:ℕ):ℝ):=by exact_mod_cast (show 1≤(r+1)+3 by omega)
  have hprod:0≤rho*t:=mul_nonneg hrho.le ht.le
  have htprod:0≤((((r+1)+3:ℕ):ℝ)-1)*t:=mul_nonneg (sub_nonneg.mpr hr) ht.le
  have hrhoprod:0≤((((r+1)+3:ℕ):ℝ)-1)*(rho*t):=mul_nonneg (sub_nonneg.mpr hr) hprod
  have hrt:rho*t≤t:=by nlinarith [mul_nonneg (sub_nonneg.mpr hrho1) ht.le]
  have htle:t≤1:=by nlinarith
  dsimp only [pstar]
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith
end Oberwolfach
