module

public import Oberwolfach.MarkedAdaptiveFailureBudget

@[expose] public section
/-! A strict gap between the common-event and matching failure budgets
leaves room for the deeper-balance event and its vanishing error. -/
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace Oberwolfach

theorem matching_deeper_failure_budget
    (εPrior ε₀:ℝ) (hgap:εPrior<ε₀):
    ∃ χ:ℝ,0<χ ∧ ∀ Qexp:ℝ,0<Qexp→∃N:ℕ,∀n:ℕ,N≤n→
      εPrior+2*χ+2*(n:ℝ)^(-Qexp)≤ε₀ := by
  let χ:ℝ:=(ε₀-εPrior)/4
  have hχ:0<χ:=by dsimp [χ];linarith
  have hslack:0<ε₀-(εPrior+2*χ):=by dsimp [χ];linarith
  refine ⟨χ,hχ,?_⟩
  intro Qexp hQexp
  have h1:Tendsto (fun n:ℕ=>(n:ℝ)^(-Qexp)) atTop (𝓝 0):=
    (tendsto_rpow_neg_atTop hQexp).comp tendsto_natCast_atTop_atTop
  have ht:Tendsto (fun n:ℕ=>2*((n:ℝ)^(-Qexp))) atTop (𝓝 0):=by
    simpa only [mul_zero] using h1.const_mul (2:ℝ)
  have he:∀ᶠ n:ℕ in atTop,2*((n:ℝ)^(-Qexp))<ε₀-(εPrior+2*χ):=
    ht.eventually (eventually_lt_nhds hslack)
  obtain ⟨N,hN⟩:=eventually_atTop.mp he
  refine ⟨N,?_⟩
  intro n hn
  have hh:=hN n hn
  linarith
end Oberwolfach
