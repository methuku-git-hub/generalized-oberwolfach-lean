module

public import Oberwolfach.FactorRemovalMargin

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
/-- In a nonempty host, the same budget leaves positive residual degree. -/
theorem factor_small_removal_positive_degree (D h n:ℕ) (hn:0<n) (δ α:ℝ)
    (hδ:0≤δ) (hα:0<α)
    (hdegree:(δ+α)*(n:ℝ)≤D) (hsmall:(h:ℝ)≤α*n/500):
    2*h<D:=by
  have hn':(0:ℝ)<n:=by exact_mod_cast hn
  have ha:0<α*n:=mul_pos hα hn'
  have hd:0≤δ*n:=mul_nonneg hδ hn'.le
  have hh:(2:ℝ)*h<D:=by nlinarith
  exact_mod_cast hh
end Oberwolfach
