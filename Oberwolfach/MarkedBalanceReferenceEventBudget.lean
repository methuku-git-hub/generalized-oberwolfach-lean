module

public import Oberwolfach.MarkedReferenceExplicitFailureBudget

@[expose] public section
/-! A concrete order threshold for combining the reference and balance events. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_reference_event_three_quarters
    {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (E:Ω→Prop) (n:ℕ) (hn:100≤n)
    (hprob:1-(1/10:ℝ)-5*(n:ℝ)^(-(1:ℝ))-9*(n:ℝ)^(-(1:ℝ))≤μ.probability E):
    (3/4:ℝ)≤μ.probability E:=by
  have hnpos:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  have hn100:(100:ℝ)≤n:=by exact_mod_cast hn
  have hpow:(n:ℝ)^(-(1:ℝ))=1/(n:ℝ):=by
    rw [Real.rpow_neg hnpos.le,Real.rpow_one,one_div]
  have hdiv:(14:ℝ)/(n:ℝ)≤7/50:=by
    apply (div_le_iff₀ hnpos).2
    linarith
  have h14:(14:ℝ)*(1/(n:ℝ))=14/(n:ℝ):=by ring
  rw [hpow] at hprob
  rw [←h14] at hdiv
  linarith only [hprob,hdiv]
end Oberwolfach
