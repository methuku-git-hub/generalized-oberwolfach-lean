module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! The discarded fraction supplies the residual interval probability and
its lower margin for the raw interval law. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_preparation_residual_bounds
    (θ rare q c d:ℝ) (hθ:0≤θ) (hθ1:θ≤1)
    (hrare:0≤rare) (hrareSmall:rare≤θ/100)
    (hq:0≤q) (hqUpper:q≤1/c) (hd:0<d) (hcut:(1/c)/d≤θ):
    let u:=θ+(1-θ)*rare;
    θ≤u ∧ u≤2*θ ∧ q/d≤u:=by
  intro u
  have hrem:0≤(1-θ)*rare:=mul_nonneg (by linarith) hrare
  have hremUpper:(1-θ)*rare≤rare:=by nlinarith
  have hqdiv:q/d≤(1/c)/d:=div_le_div_of_nonneg_right hqUpper hd.le
  dsimp [u]
  constructor
  · linarith
  constructor
  · nlinarith [hremUpper,hrareSmall]
  · linarith [hqdiv,hcut]
end Oberwolfach
