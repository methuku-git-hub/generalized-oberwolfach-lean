module

public import Oberwolfach.OrdinaryDeepParentBalanceFailureBudget

@[expose] public section
/-! The original failure tolerance supplies one positive allowance for all
matching, correction, deep, parent and three-step events. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_parent_equal_failure_allowances (χ:ℝ) (hχ:0<χ):
    ∃t:ℝ,0<t ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (E:Ω→Prop),
      1-(23*t+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2))≤μ.probability E→
      1-χ-1/(n:ℝ)^10≤μ.probability E :=by
  obtain ⟨cap,hcap,N,hN,hbudget⟩:=ordinary_deep_parent_balance_failure_cap χ hχ
  let t:=cap/2
  have ht:0<t:=by dsimp [t]; positivity
  have htc:t≤cap:=by dsimp [t]; linarith
  refine ⟨t,ht,N,hN,?_⟩
  intro n hn Ω _ μ E hprob
  apply hbudget n hn 0 t t t t t t t t t t t t
    (by linarith) htc htc htc htc htc htc htc htc htc htc htc htc
    t t t t t t t t htc htc htc htc htc htc htc htc Ω μ E
  linarith only [hprob]
end Oberwolfach
