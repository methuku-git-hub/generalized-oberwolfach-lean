module

public import Oberwolfach.OrdinarySharpBufferedRootScaleChoice

@[expose] public section
/-! Small protected-root and cover-load coefficients fit the separate
physical-edit margin, independently of the later balance margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sharp_root_edit_margins
    (m:ℕ) (edit lam κ:ℝ) (hedit:0<edit) (hlam:0≤lam) (hκ:0≤κ)
    (hrow:3*lam≤edit/4) (hlevel:lam*((m:ℝ)+1)≤edit/4)
    (hκcap:κ≤edit/(72*((m:ℝ)+2))):
    18*κ+3*lam≤edit/2 ∧ (3*κ+lam)*((m:ℝ)+1)≤edit/2:=by
  have hm:0≤(m:ℝ):=Nat.cast_nonneg _
  have hden:0<72*((m:ℝ)+2):=by positivity
  have hmul:κ*(72*((m:ℝ)+2))≤edit:=(le_div_iff₀ hden).mp hκcap
  have hκm:0≤κ*(m:ℝ):=mul_nonneg hκ hm
  constructor <;> nlinarith only [hmul,hrow,hlevel,hκ,hκm]
end Oberwolfach
