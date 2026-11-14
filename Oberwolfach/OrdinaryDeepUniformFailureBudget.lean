module

public import Oberwolfach.OrdinaryDeepParentBalanceFailureBudget

@[expose] public section
/-! A single positive allowance controls every matching, correction,
parent, deep and three-step balance failure in the nontriangle case. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_uniform_failure_budget (χ:ℝ) (hχ:0<χ):
    ∃t:ℝ,0<t ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Event:Ω→Prop),
    let loss:=(((((((0+3*t+t)+2*t)+t)+t)+t)+t)+t);
    1-(loss+t+t+t+t+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+t+t+t+t+t)-t-t-t≤μ.probability Event→
    1-χ-1/(n:ℝ)^10≤μ.probability Event :=by
  obtain ⟨t,ht,N,hN,hbudget⟩:=ordinary_deep_parent_balance_failure_cap χ hχ
  refine ⟨t,ht,N,hN,?_⟩
  intro n hn Ω _ μ Event loss hprob
  exact hbudget n hn 0 t t t t t t t t t t t t
    ht.le (le_refl t) (le_refl t) (le_refl t) (le_refl t) (le_refl t) (le_refl t) (le_refl t)
    (le_refl t) (le_refl t) (le_refl t) (le_refl t) (le_refl t)
    t t t t t t t t (le_refl t) (le_refl t) (le_refl t) (le_refl t)
    (le_refl t) (le_refl t) (le_refl t) (le_refl t) Ω μ Event hprob
end Oberwolfach
