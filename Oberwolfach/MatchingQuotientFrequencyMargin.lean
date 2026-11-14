module

public import Oberwolfach.MatchingFrequencyMargin

@[expose] public section
/-! A bound stated after division by the wheel size has the same uniform
absolute error as the undivided matching estimate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem matching_frequency_quotient_margin
    (r actual n θ f error γ ε:ℝ)
    (hr:1≤r) (hn:0≤n) (hε:0≤ε) (hε1:ε≤1) (hγ:0≤γ) (hγε:γ≤ε)
    (he0:0≤error) (he:error≤ε*n) (htarget:|(1-θ)*f*n|≤n)
    (h:|actual-(1-θ)*f*n/r|≤(error+γ*(|(1-θ)*f*n|+error))/r):
    |actual-(1-θ)*f*n/r|≤3*ε*n :=by
  have ht0:0≤|(1-θ)*f*n|:=abs_nonneg _
  have hfirst:γ*(|(1-θ)*f*n|+error)≤ε*(n+ε*n):=by
    apply le_trans (mul_le_mul_of_nonneg_left (add_le_add htarget he) hγ)
    apply mul_le_mul_of_nonneg_right hγε
    positivity
  have hprod:ε*(ε*n)≤ε*n:=by
    have hh:=mul_le_mul_of_nonneg_right hε1 (mul_nonneg hε hn)
    nlinarith
  have hnum:error+γ*(|(1-θ)*f*n|+error)≤3*ε*n:=by nlinarith
  have hdiv:(error+γ*(|(1-θ)*f*n|+error))/r≤3*ε*n:=by
    apply (div_le_iff₀ (by linarith : 0<r)).2
    have hh:=mul_le_mul_of_nonneg_left hr (show 0≤3*ε*n by positivity)
    nlinarith
  exact h.trans hdiv
end Oberwolfach

namespace Oberwolfach

theorem hub_frequency_error_budget
    (q n η ηmax err countErr eps:ℝ)
    (hq:0≤q) (hqn:q≤n) (hη:0≤η) (hη1:η≤ηmax)
    (herr:0≤err) (herrle:err≤eps/2) (hcount:0≤countErr)
    (hcountle:ηmax*countErr≤(eps/2)*n):
    0≤q*err+η*countErr ∧ q*err+η*countErr≤eps*n :=by
  constructor
  · positivity
  · have h₁:q*err≤n*(eps/2):=by
      have ha:=mul_le_mul_of_nonneg_right hqn herr
      have hb:=mul_le_mul_of_nonneg_left herrle (show (0:ℝ)≤n from hq.trans hqn)
      exact ha.trans hb
    have h₂:=mul_le_mul_of_nonneg_right hη1 hcount
    nlinarith
end Oberwolfach
