module

public import Oberwolfach.OrdinaryGeneralFinishOrderedHierarchy

@[expose] public section
/-! The currently available coarse outside-degree bound cannot itself
supply the much smaller sampled-class change budget.  A finer bound is
required; this is an algebraic diagnostic, not an extra assumption. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_root_cover_coarse_budget_barrier
    (x y a n c ell:ℝ) (hx:0<x) (hy:0≤y) (hyx:y≤x)
    (hc0:0≤c) (hc1:c≤1) (hsize:x≤a*n)
    (hell:18*a*n≤ell):
    ¬ell≤c*y:=by
  have hcy:c*y≤y:=by
    have hh:=mul_nonneg hy (sub_nonneg.mpr hc1)
    nlinarith only [hh]
  intro h
  linarith only [hx,hyx,hsize,hell,hcy,h]
end Oberwolfach
