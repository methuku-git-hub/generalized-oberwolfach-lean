module

public import Oberwolfach.OrdinaryGlobalBalanceFromSample

@[expose] public section
/-! Choose the global row-test tolerance before the host and absorb the
fixed conflict degree into the balance error at sufficiently large order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_global_balance_uniform_margin
    (η:ℝ) (hη:0<η):
    ∃ε:ℝ,0<ε ∧ ∀L:ℝ,0≤L→∃N:ℕ,1≤N ∧ ∀n u:ℕ,N≤n→u≤n→
      ε*n+2*(ε*u)+3*L≤η*n :=by
  refine ⟨η/12,by positivity,?_⟩
  intro L hL
  obtain ⟨M,hM⟩:=exists_nat_gt (6*L/η)
  refine ⟨max M 1,by omega,?_⟩
  intro n u hn hu
  have hMn:(M:ℝ)≤n:=by exact_mod_cast (show M≤n by omega)
  have hlarge:6*L/η≤(n:ℝ):=hM.le.trans hMn
  have hlarge':6*L≤(n:ℝ)*η:=(div_le_iff₀ hη).mp hlarge
  have hun:(u:ℝ)≤n:=by exact_mod_cast hu
  have hh:=mul_le_mul_of_nonneg_left hun hη.le
  have hnη:0≤η*(n:ℝ):=by positivity
  nlinarith only [hlarge',hh,hnη]
end Oberwolfach
