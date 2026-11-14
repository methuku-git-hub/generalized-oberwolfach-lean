module

public import Oberwolfach.OrdinarySelectedParentEventRates

@[expose] public section
/-! The selected beta and row caps, together with the two parent-rate
bounds, supply the shared initial and later numerical inequalities. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_selected_wheel_arithmetic_inputs
    (αOriginal β βcap γgeom δcap εR εH ε eParent hParent cBoundary cInitial:ℝ)
    (hα:0<αOriginal) (hβ:β≤αOriginal/8) (hβcap:β≤βcap) (hβγ:βcap≤γgeom/1000)
    (hR:εR≤δcap) (hH:εH≤δcap) (hδγ:δcap≤γgeom/1000)
    (hε:0<ε) (he:0<eParent) (hh:0<hParent)
    (heBoundary:eParent≤cBoundary) (hhBoundary:hParent≤cBoundary)
    (heInitial:eParent≤cInitial) (hhInitial:hParent≤cInitial):
    β≤2*(αOriginal/2) ∧ β≤γgeom/1000 ∧ εR≤γgeom/1000 ∧ εH≤γgeom/1000 ∧
    0≤eParent*ε ∧ eParent*ε≤cBoundary*ε ∧ eParent*ε≤cInitial*ε ∧
    0≤hParent*ε ∧ hParent*ε≤cBoundary*ε ∧ hParent*ε≤cInitial*ε :=by
  have hβa:β≤2*(αOriginal/2):=by linarith
  exact ⟨hβa,hβcap.trans hβγ,hR.trans hδγ,hH.trans hδγ,
    mul_nonneg he.le hε.le,mul_le_mul_of_nonneg_right heBoundary hε.le,mul_le_mul_of_nonneg_right heInitial hε.le,
    mul_nonneg hh.le hε.le,mul_le_mul_of_nonneg_right hhBoundary hε.le,mul_le_mul_of_nonneg_right hhInitial hε.le⟩
end Oberwolfach
