module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! Uniform failure budgets for the full adaptive event, including agreement. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter
open scoped Topology
noncomputable section
namespace Oberwolfach

theorem eventually_marked_adaptive_agreement_failure_below
    (χ χCommon χBal χNbr χLoad χLocal χConfig Qexp ε₀:ℝ) (Qpow:ℕ)
    (hQexp:0<Qexp) (hQpow:0<Qpow)
    (hgap:χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig<ε₀):
    ∃N:ℕ,∀n:ℕ,N≤n→
      χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+
        7*(n:ℝ)^(-Qexp)+5/(n:ℝ)^Qpow<ε₀ :=by
  have h1:Tendsto (fun n:ℕ=>(n:ℝ)^(-Qexp)) atTop (𝓝 0):=
    (tendsto_rpow_neg_atTop hQexp).comp tendsto_natCast_atTop_atTop
  have hq:0<(Qpow:ℝ):=by exact_mod_cast hQpow
  have h2':Tendsto (fun n:ℕ=>(n:ℝ)^(-(Qpow:ℝ))) atTop (𝓝 0):=
    (tendsto_rpow_neg_atTop hq).comp tendsto_natCast_atTop_atTop
  have h2:Tendsto (fun n:ℕ=>1/(n:ℝ)^Qpow) atTop (𝓝 0):=by
    convert h2' using 1
    funext n
    rw [Real.rpow_neg (Nat.cast_nonneg n),Real.rpow_natCast]
    simp
  have ht:Tendsto (fun n:ℕ=>7*((n:ℝ)^(-Qexp))+5/(n:ℝ)^Qpow) atTop (𝓝 0):=by
    simpa only [mul_zero,zero_add,div_eq_mul_inv,one_mul] using (h1.const_mul 7).add (h2.const_mul 5)
  have hg:0<ε₀-(χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig):=by linarith
  have he:∀ᶠn:ℕ in atTop,7*((n:ℝ)^(-Qexp))+5/(n:ℝ)^Qpow<ε₀-(χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig):=
    ht.eventually (eventually_lt_nhds hg)
  obtain ⟨N,hN⟩:=eventually_atTop.mp he
  refine ⟨N,?_⟩
  intro n hn
  have hh:=hN n hn
  linarith

theorem marked_adaptive_agreement_failure_budgets_exist
    (Qexp ε₀:ℝ) (Qpow:ℕ) (hQexp:0<Qexp) (hQpow:0<Qpow) (hε₀:0<ε₀):
    ∃χ χCommon χBal χNbr χLoad χLocal χConfig:ℝ,
      0<χ ∧ 0<χCommon ∧ 0<χBal ∧ 0<χNbr ∧ 0<χLoad ∧ 0<χLocal ∧ 0<χConfig ∧
      ∃N:ℕ,∀n:ℕ,N≤n→
        χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+
          7*(n:ℝ)^(-Qexp)+5/(n:ℝ)^Qpow<ε₀ :=by
  let e:=ε₀/16
  have he:0<e:=by dsimp [e];positivity
  have hgap:e+e+e+2*e+e+e+e<ε₀:=by dsimp [e];linarith
  obtain ⟨N,hN⟩:=eventually_marked_adaptive_agreement_failure_below e e e e e e e Qexp ε₀ Qpow hQexp hQpow hgap
  exact ⟨e,e,e,e,e,e,e,he,he,he,he,he,he,he,N,hN⟩
end Oberwolfach
