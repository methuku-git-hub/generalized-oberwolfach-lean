module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! The named reference-and-absorber event has a uniform fixed failure budget
once its constant terms lie strictly below that budget. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter
open scoped Topology
noncomputable section
namespace Oberwolfach

theorem eventually_marked_reference_absorber_failure_below
    (χ χActive Qexp ε₀:ℝ) (Qpow:ℕ) (hQexp:0<Qexp) (hQpow:0<Qpow)
    (hgap:χ+2*χActive<ε₀):
    ∃N:ℕ,∀n:ℕ,N≤n→
      χ+2*χActive+2*(n:ℝ)^(-Qexp)+2/(n:ℝ)^Qpow<ε₀ :=by
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
  have ht:Tendsto (fun n:ℕ=>2*((n:ℝ)^(-Qexp))+2/(n:ℝ)^Qpow) atTop (𝓝 0):=by
    simpa only [mul_zero,zero_add,div_eq_mul_inv,one_mul] using (h1.const_mul 2).add (h2.const_mul 2)
  have hg:0<ε₀-(χ+2*χActive):=by linarith
  have he:∀ᶠn:ℕ in atTop,2*((n:ℝ)^(-Qexp))+2/(n:ℝ)^Qpow<ε₀-(χ+2*χActive):=
    ht.eventually (eventually_lt_nhds hg)
  obtain ⟨N,hN⟩:=eventually_atTop.mp he
  refine ⟨N,?_⟩
  intro n hn
  have hh:=hN n hn
  linarith
end Oberwolfach
