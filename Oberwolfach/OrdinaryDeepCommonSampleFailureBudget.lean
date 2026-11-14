module

public import Oberwolfach.OrdinaryDeepUniformFailureBudget

@[expose] public section
/-! The failure bound in the actual parent, correction and three-step
balance bundle fits the single allowance without a second event loss. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_common_sample_failure_budget (χ:ℝ) (hχ:0<χ):
    ∃t:ℝ,0<t ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Event:Ω→Prop),
    let loss0:=(((((((0+3*t+t)+2*t)+t)+t)+t)+t)+t);
    let loss:=loss0+t+t+t+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+t;
    1-(loss+t+t+t+t+t)-t-t-t≤μ.probability Event→
    1-χ-1/(n:ℝ)^10≤μ.probability Event :=by
  obtain ⟨t,ht,N,hN,hbudget⟩:=ordinary_deep_uniform_failure_budget χ hχ
  refine ⟨t,ht,N,hN,?_⟩
  intro n hn Ω _ μ Event loss0 loss hprob
  apply hbudget n hn Ω μ Event
  dsimp [loss,loss0] at *
  linarith only [hprob]
end Oberwolfach
