module

public import Oberwolfach.LongCommonIncidenceParameterBudget

@[expose] public section
/-! The existing common-event hierarchy makes both matching defects small. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_matching_error_budget
    (lam θ eps:ℝ) (d K:ℕ) (hlam:0≤lam) (hlam1:lam≤1) (hθ:0≤θ) (hK:5≤K)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    max a γ≤θ/4096:=by
  intro a γ
  have hK5:(5:ℝ)≤K:=by exact_mod_cast hK
  have hKpos:0<(K:ℝ):=by linarith
  have hden:0<100*(K:ℝ)^2:=by positivity
  have hmass:θ/(100*(K:ℝ)^2)≥0:=div_nonneg hθ hden.le
  have heps':eps≤θ/(300*(K:ℝ)^2):=by
    have hh:lam*(θ/(100*(K:ℝ)^2))≤θ/(100*(K:ℝ)^2):=by nlinarith
    have heq:θ/(100*(K:ℝ)^2)=3*(θ/(300*(K:ℝ)^2)):=by ring
    linarith
  have ha:a≤θ/(200*(K:ℝ)^2):=min_le_right _ _
  have hg:γ≤eps/2:=min_le_left _ _
  have hscale:θ/(200*(K:ℝ)^2)≤θ/4096:=by
    apply (div_le_iff₀ (by positivity : 0<200*(K:ℝ)^2)).2
    nlinarith [sq_nonneg ((K:ℝ)-5)]
  have hscale':θ/(300*(K:ℝ)^2)≤θ/4096:=by
    apply (div_le_iff₀ (by positivity : 0<300*(K:ℝ)^2)).2
    nlinarith [sq_nonneg ((K:ℝ)-5)]
  apply max_le
  · exact ha.trans hscale
  · have hh:=heps'.trans hscale'
    linarith
end Oberwolfach
