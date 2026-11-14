module

public import Oberwolfach.MarkedAdaptiveFailureBudget

@[expose] public section
/-! Choose a uniform extra-event allowance before the graph order. -/
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace Oberwolfach

theorem reference_extra_failure_budget (εExtra:ℝ) (hε:0<εExtra):
    ∃ χ:ℝ,0<χ ∧ ∃N:ℕ,∀n:ℕ,N≤n→
      100*χ+100*(n:ℝ)^(-(1:ℝ))≤εExtra := by
  let χ:=εExtra/400
  have hχ:0<χ:=by dsimp [χ];positivity
  have hslack:0<εExtra-100*χ:=by dsimp [χ];linarith
  have h1:Tendsto (fun n:ℕ=>(n:ℝ)^(-(1:ℝ))) atTop (𝓝 0):=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp tendsto_natCast_atTop_atTop
  have ht:Tendsto (fun n:ℕ=>100*((n:ℝ)^(-(1:ℝ)))) atTop (𝓝 0):=by
    simpa only [mul_zero] using h1.const_mul (100:ℝ)
  have he:∀ᶠ n:ℕ in atTop,100*((n:ℝ)^(-(1:ℝ)))<εExtra-100*χ:=
    ht.eventually (eventually_lt_nhds hslack)
  obtain ⟨N,hN⟩:=eventually_atTop.mp he
  refine ⟨χ,hχ,N,?_⟩
  intro n hn
  have hh:=hN n hn
  linarith
end Oberwolfach
