module

public import Oberwolfach.ReservedSpokeListMargins

@[expose] public section
/-! A reserved-pair matching density independent of θ. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem reserved_pair_margin_choice (ρ₀:ℝ) (hρ₀:0<ρ₀):
    ∃α:ℝ,0<α ∧ ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U]
      (inner:Finset U) (ρ D:ℝ),ρ₀≤ρ→(n:ℝ)/2≤D→ρ*D=2*Fintype.card U→
      (inner.card:ℝ)≤α*n→
      α*n+inner.card≤(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ):=by
  let c:ℝ:=(5/8:ℝ)*(1/100:ℝ)^2
  let α:ℝ:=c*ρ₀/16
  have hc:0<c:=by dsimp [c];norm_num
  have hα:0<α:=by dsimp [α];positivity
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear α 0 hα
  refine ⟨α,hα,N,?_⟩
  intro n hn U _ inner ρ D hρ hD hsize hinner
  have hnR:(0:ℝ)≤n:=by positivity
  have hD0:0≤D:=by linarith
  have hρD:=mul_le_mul_of_nonneg_right hρ hD0
  have hDn:=mul_le_mul_of_nonneg_left hD hρ₀.le
  have hU:ρ₀*n/4≤(Fintype.card U:ℝ):=by nlinarith
  have hmul:=mul_le_mul_of_nonneg_left hU hc.le
  have herr:=hN n hn
  have hαn:4*α*n=c*(ρ₀*n/4):=by dsimp [α];ring
  dsimp only [c] at *
  nlinarith
end Oberwolfach
