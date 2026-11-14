module

public import Oberwolfach.OrdinaryParentRootPackingSlack

@[expose] public section
/-! The parent event uses the full selected rates, while the local
certificate uses their half-rate cleanup budgets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_selected_parent_event_rates
    (eParent hParent cBoundary ε:ℝ)
    (he:0<eParent) (hh:0<hParent) (hε:0<ε)
    (hecap:eParent≤cBoundary) (hhcap:hParent≤cBoundary):
    0≤eParent*ε ∧ eParent*ε≤cBoundary*ε ∧
    0≤hParent*ε ∧ hParent*ε≤cBoundary*ε ∧
    0≤(eParent/2)*ε ∧ 0≤(hParent/2)*ε :=by
  exact ⟨mul_nonneg he.le hε.le,mul_le_mul_of_nonneg_right hecap hε.le,
    mul_nonneg hh.le hε.le,mul_le_mul_of_nonneg_right hhcap hε.le,
    mul_nonneg (by positivity) hε.le,mul_nonneg (by positivity) hε.le⟩
end Oberwolfach
