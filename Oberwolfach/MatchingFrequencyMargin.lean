module

public import Oberwolfach.MatchingFrequencyError

@[expose] public section
/-! An explicit numerical margin for turning the frequency error into an
additive error linear in the number of vertices. -/
set_option autoImplicit false
namespace Oberwolfach

theorem matching_frequency_margin
    (r actual η s n θ f error γ ε:ℝ)
    (hr:1≤r) (hn:0≤n) (hε:0≤ε) (hε1:ε≤1) (hγ:0≤γ) (hγε:γ≤ε)
    (he0:0≤error) (he:error≤ε*n) (htarget:|(1-θ)*f*n|≤n)
    (hbalance:η*s=(1-θ)*f)
    (h:|r*actual-η*s*n|≤error+γ*(|η*s*n|+error)):
    |actual-(1-θ)*f*n/r|≤3*ε*n :=by
  have h₁:=matching_frequency_error r actual η s n θ f error γ (by linarith) hbalance h
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
  exact h₁.trans hdiv
end Oberwolfach
