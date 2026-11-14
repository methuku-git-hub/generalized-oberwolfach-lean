module

public import Oberwolfach.LongRetainedHubCoefficient

@[expose] public section
/-! A common numerical choice for the hub-frequency and retained-test
margins. All constants depend only on the displayed fixed parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_hub_frequency_parameters (K:ℕ) (θ lam pstar:ℝ)
    (hK:0<K) (hθ0:0<θ) (hθ1:θ≤1/2) (hlam0:0<lam) (hlamθ:lam≤θ)
    (hp:0<pstar) :
    ∃eps t τ γ:ℝ, 0<eps ∧ eps≤1 ∧ 0≤t ∧ 0≤τ ∧ 0≤γ ∧ γ≤eps ∧
      t+4*τ≤eps/2 ∧ t≤θ/(800*(K:ℝ)) ∧
      3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧ eps≤4*pstar :=by
  have hK0:0<(K:ℝ):=by exact_mod_cast hK
  have hK1:1≤(K:ℝ):=by exact_mod_cast hK
  have hK2:0<(K:ℝ)^2:=by positivity
  let eps:ℝ:=min (pstar/2) (min (lam*θ/(600*(K:ℝ)^2)) (1/2))
  have heps:0<eps:=by dsimp [eps];positivity
  have heps1:eps≤1/2:=le_trans (min_le_right _ _) (min_le_right _ _)
  have hepsp:eps≤pstar/2:=min_le_left _ _
  have hepsc:eps≤lam*θ/(600*(K:ℝ)^2):=le_trans (min_le_right _ _) (min_le_left _ _)
  refine ⟨eps,eps/4,eps/16,eps,heps,by linarith,by positivity,by positivity,by positivity,le_refl _,by linarith,?_,?_,by linarith⟩
  · have hLam:lam≤1:=by linarith
    have hθk:0≤θ*(K:ℝ):=by positivity
    apply (le_div_iff₀ (by positivity : (0:ℝ)<800*(K:ℝ))).2
    have hc : eps*(600*(K:ℝ)^2)≤lam*θ:= (le_div_iff₀ (by positivity)).1 hepsc
    nlinarith [sq_nonneg ((K:ℝ)-1)]
  · have hc : eps*(600*(K:ℝ)^2)≤lam*θ:= (le_div_iff₀ (by positivity)).1 hepsc
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0:ℝ)<100*(K:ℝ)^2)).2
    nlinarith
end Oberwolfach

namespace Oberwolfach

theorem long_hub_count_error_budget (n eps pstar:ℝ)
    (hn:0≤n) (heps:0≤eps) (hp:0≤pstar) (hsmall:eps≤4*pstar):
    0≤eps*n/8 ∧ 4*(eps*n/8)≤(eps/2)*n ∧ eps*n/8≤pstar*n/2 :=by
  constructor
  · positivity
  constructor
  · ring_nf
    exact le_rfl
  · have h:=mul_le_mul_of_nonneg_right hsmall hn
    nlinarith
end Oberwolfach
