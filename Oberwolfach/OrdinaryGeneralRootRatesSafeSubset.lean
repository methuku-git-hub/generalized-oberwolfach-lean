module

public import Oberwolfach.OrdinaryGeneralRootCoverBudget

@[expose] public section
/-! Uniform ambient error-rate bounds and the deep-set bound needed by the
    general root-first completion follow from the geometric root-size bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_general_root_rates_from_geometry_safe_subset
    (m:ℕ) (cap κ lam ξ βe N Nsum I T W:ℝ)
    (hcap:0<cap) (hκ:0≤κ) (hlam:0≤lam) (hξ:0≤ξ) (hβe:0≤βe)
    (hN:0≤N) (hNsum:N≤Nsum) (hI:0≤I) (hIcap:I≤N)
    (hT:0≤T) (hW:0≤W) (hroots:T+W≤lam*N)
    (hκcap:κ≤cap/(1000*((m:ℝ)+2))) (hlamcap:lam≤cap/(1000*((m:ℝ)+2)))
    (hξcap:10*ξ≤cap) (hsmall:lam≤βe/4):
    let ell:=max (18*κ*N+3*(W+T)) (3*κ*N*((m:ℝ)+1)+T*((m:ℝ)+1));
    0≤ell ∧ ell≤cap*Nsum ∧ 10*ξ*I≤cap*Nsum ∧ T≤(βe/4)*Nsum :=by
  intro ell
  have hbudget:=ordinary_general_root_cover_budget m cap κ lam 0 0 N N 0 T W hcap hκ hlam (by norm_num) (by norm_num)
    hN (by linarith) (by norm_num) (by simp) hT hW hroots hκcap hlamcap (by nlinarith [hcap])
  have hell0:0≤ell:=hbudget.1
  have hellN:ell≤cap*N:=hbudget.2.2.2.2.2.2
  have hCN:cap*N≤cap*Nsum:=mul_le_mul_of_nonneg_left hNsum hcap.le
  have hξI:10*ξ*I≤cap*N:=by
    have h1:=mul_le_mul_of_nonneg_right hξcap hI
    have h2:=mul_le_mul_of_nonneg_left hIcap hcap.le
    nlinarith only [h1,h2]
  have hsmall0:0≤βe/4:=by positivity
  have hTn:T≤(βe/4)*Nsum:=by
    have h1:=mul_le_mul_of_nonneg_right hsmall hN
    have h2:=mul_le_mul_of_nonneg_left hNsum hsmall0
    linarith
  exact ⟨hell0,hellN.trans hCN,hξI.trans hCN,hTn⟩
end Oberwolfach
