module

public import Mathlib.Tactic

@[expose] public section
/-! A quadratic deeper-set ratio fits inside a linearly scaled cleanup
    margin; no factor of the fresh retention probability is needed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_safe_deeper_ratio_linear (ε ce βe:ℝ)
    (hε:0<ε) (hce:0<ce) (hεsmall:ε≤ce/8) (hmargin:ce*ε≤βe):
    ∃lam:ℝ,0<lam ∧ 2*ε^2≤lam ∧ lam≤βe/4 :=by
  refine ⟨2*ε^2,by positivity,le_rfl,?_⟩
  have hh:=mul_nonneg hε.le (sub_nonneg.mpr hεsmall)
  nlinarith only [hh,hmargin]
end Oberwolfach
