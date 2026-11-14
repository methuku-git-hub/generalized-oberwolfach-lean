module

public import Oberwolfach.MarkedIterationToleranceUniformDensities

@[expose] public section
/-! Fixed lower bounds in the uniform interfaces are valid whenever the
original density inequalities have an admissible realization. -/
set_option autoImplicit false
namespace Oberwolfach

theorem marked_uniform_density_bounds_automatic
    (r:ℕ) (rho₀ omega₀ t₀ rho omega t p0:ℝ)
    (hr:2≤r) (hrho₀:0<rho₀) (hρ:rho₀≤rho) (hrho1:rho≤1)
    (ho₀:0<omega₀) (hω:omega₀≤omega) (ho1:omega≤1)
    (ht₀:0<t₀) (htlo:t₀≤t) (ht1:(r+4:ℝ)*t≤1)
    (hp0:0<p0) (hp:p0≤rho*(r+4:ℝ)*t/2):
    rho₀≤1 ∧ omega₀≤1 ∧ t₀≤1 ∧ p0≤1/2:=by
  have hrho:0<rho:=hrho₀.trans_le hρ
  have ht:0<t:=ht₀.trans_le htlo
  have hr0:(0:ℝ)≤r:=Nat.cast_nonneg r
  have ht_le:t≤1:=by nlinarith only [ht1,hr0,ht]
  have hp_le:rho*((r+4:ℝ)*t)≤1:=by
    have hh:=mul_le_mul_of_nonneg_left ht1 hrho.le
    nlinarith only [hh,hrho1]
  refine ⟨hρ.trans hrho1,hω.trans ho1,htlo.trans ht_le,?_⟩
  nlinarith only [hp,hp_le]
end Oberwolfach
