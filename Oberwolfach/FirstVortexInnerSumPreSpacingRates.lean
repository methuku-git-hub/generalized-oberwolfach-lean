module

public import Oberwolfach.FirstVortexInnerSumRateChoice
public import Oberwolfach.FirstVortexInnerSumFiniteErrors

@[expose] public section
/-! Fix the inner and outer rates after the balance cap, then a uniform host
threshold for all fixed and sublinear errors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_inner_sum_pre_spacing_rates
    (ε c rho eta cap:ℝ) (hε:0<ε) (hc:0<c) (hrho:0<rho) (heta:0<eta) (hcap:0<cap):
    ∃t s:ℝ,0<t ∧ t≤cap ∧ 0<s ∧ 32*s≤t ∧
      5*t≤ε*eta/2 ∧ 5*t≤c*rho*ε/8 ∧ (17+2/rho)*t≤c*ε/4 ∧
      ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→0<n ∧
        ((6*d+2:ℕ):ℝ)≤s*n ∧ 1≤s*n ∧ 1≤t*n ∧
        (n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ)≤(t/4)*n ∧
        (n:ℝ)^(3/5:ℝ)≤(t/4)*n :=by
  obtain ⟨t,ht,htcap,hglobal,hlocal,htransfer⟩:=first_vortex_inner_sum_rate_choice ε c rho eta cap hε hc hrho heta hcap
  let s:=t/32
  have hs:0<s:=by dsimp [s];positivity
  have hst:32*s≤t:=by dsimp [s];linarith
  refine ⟨t,s,ht,htcap,hs,hst,hglobal,hlocal,htransfer,?_⟩
  intro d
  obtain ⟨N,hN⟩:=first_vortex_inner_sum_finite_errors d s (t/4) hs (by positivity)
  refine ⟨max N 1,?_⟩
  intro n hn
  have hnN:N≤n:=le_trans (le_max_left _ _) hn
  have hn1:1≤n:=le_trans (le_max_right _ _) hn
  have hpos:0<n:=by omega
  obtain ⟨hfixed,hunit,hpow⟩:=hN n hnN
  have hnR:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hsle:s≤t:=by dsimp [s];linarith
  have hunitT:1≤t*n:=hunit.trans (mul_le_mul_of_nonneg_right hsle hnR)
  have hpow0:0≤(d:ℝ)*(n:ℝ)^(3/5:ℝ):=by positivity
  exact ⟨hpos,hfixed,hunit,hunitT,hpow,by linarith⟩
end Oberwolfach
