module

public import Oberwolfach.MarkedBalancePerturbationSlack
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
/-! The explicit ambient-change slack used for inner balance cannot be
combined with a global-loss parameter at least as large as the vortex scale.
This is an obstruction to that quantitative route, not to the target theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_explicit_balance_scale_obstruction
    (m:ℕ) (ε iota etaBal x cap δglobal:ℝ)
    (hε:0<ε) (hiota:0< iota) (hiotaε:iota≤ε)
    (hη:0<etaBal) (hη1:etaBal≤1) (hx:0<x) (hcap:0≤cap)
    (hslack:∀ζ:ℝ,0≤ζ→ζ≤cap→∀n I err:ℝ,0≤n→iota*n≤I→
      err≤(etaBal/2)*I→err≤(x/4)*n→
      err+(m+4:ℕ)*ζ*n≤etaBal*I ∧ err+(m+4:ℕ)*ζ*n≤(x/2)*n)
    (hεglobal:ε≤δglobal)
    (hglobal:δglobal+Real.sqrt δglobal≤min cap (1:ℝ)/1024):False :=by
  have hlocal:= (hslack cap hcap le_rfl 1 iota 0 (by norm_num) (by simp)
    (by positivity) (by positivity)).1
  have hm:(1:ℝ)≤((m+4:ℕ):ℝ):=by exact_mod_cast (show 1≤m+4 by omega)
  have hc:cap≤etaBal*iota:=by nlinarith [mul_nonneg hcap (sub_nonneg.mpr hm)]
  have hproduct:etaBal*iota≤ iota:=by nlinarith [mul_nonneg hiota.le (sub_nonneg.mpr hη1)]
  have hcapε:cap≤ε:=hc.trans (hproduct.trans hiotaε)
  have hδ:δglobal≤cap/1024:=by
    have hroot:=Real.sqrt_nonneg δglobal
    have hcmin:=min_le_left cap (1:ℝ)
    linarith
  linarith
end Oberwolfach
