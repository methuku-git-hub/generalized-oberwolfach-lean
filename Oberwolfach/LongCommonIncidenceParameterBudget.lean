module

public import Oberwolfach.LongAssignedAdaptiveWeightedInnerColumn

@[expose] public section
/-! The common-event matching parameters satisfy the physical degree budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_common_incidence_parameter_budget
    (lam θ eps:ℝ) (d K:ℕ) (hlam:0≤lam) (hd:3≤d):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    2*max a (4*γ)≤lam/3:=by
  intro a γ
  have hdpos:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
  have hd3:(3:ℝ)≤d:=by exact_mod_cast hd
  have ha:a≤lam/(10*(d:ℝ)):=min_le_left _ _
  have hg:γ≤lam/(10*(d:ℝ)):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hscale:lam/(10*(d:ℝ))≤lam/30:=by
    apply (div_le_iff₀ (by positivity : 0<10*(d:ℝ))).2
    nlinarith
  have ha':a≤lam/30:=ha.trans hscale
  have hg':γ≤lam/30:=hg.trans hscale
  have hmax:max a (4*γ)≤2*lam/15:=by
    apply max_le
    · linarith
    · linarith
  linarith
end Oberwolfach
