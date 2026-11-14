module

public import Oberwolfach.FirstVortexActiveCeilingEventually

@[expose] public section
/-! Apply the selected spacing and assignment rates to the exact
first-active prescribed-set and ceiling budgets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_selector_active_budgets
    (d K:ℕ) (ρ ε cap θ lamAssign lam eps:ℝ)
    (hd:0<d) (hρ:0<ρ) (hε:0<ε) (hcap:0<cap) (hlam:lam≤1)
    (hspacing:1/(d:ℝ)≤(cap*ε/128)/10)
    (hcoeff:8*(θ*ε^2+lamAssign*ε)/((ρ/4)/40000)<cap*ε/128):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    ∃N:ℕ,∀n:ℕ,N≤n→
      2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a γ*n≤cap*(ε*n)/128 ∧
      ∀E:ℕ,(E:ℝ)≤(θ*ε^2+lamAssign*ε)*(n:ℝ)^2+24*d*n→
        2*(⌈4*(E:ℝ)/(((ρ/4)/40000)*n)⌉₊:ℕ)≤cap*(ε*n)/128 :=by
  intro a γ
  obtain ⟨N1,hN1⟩:=first_vortex_prescribed_active_eventually d K ε cap lam θ eps hd hε hcap hlam hspacing
  obtain ⟨N2,hN2⟩:=first_vortex_active_ceiling_eventually d ρ ε cap θ lamAssign hρ hε hcap hcoeff
  refine ⟨max N1 N2,?_⟩
  intro n hn
  exact ⟨hN1 n (by omega),hN2 n (by omega)⟩

theorem first_vortex_selector_incidence_small
    (d K:ℕ) (θ lam eps:ℝ) (hd:0<d) (hθ:0<θ) (hθ1:θ≤1)
    (hlam:0≤lam) (hlamθ:lam≤θ) (hspacing:1/(d:ℝ)≤θ/1024):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    max a γ≤θ/4096 :=by
  intro a γ
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  have hdiv:1≤(d:ℝ)*(θ/1024):=by
    have hh:1/(d:ℝ)≤θ/1024:=hspacing
    simpa only [mul_comm] using (div_le_iff₀ hdR).mp hh
  have hdlarge:1024≤(d:ℝ):=by nlinarith [mul_nonneg hdR.le (sub_nonneg.mpr hθ1)]
  have hbound:lam/(10*(d:ℝ))≤θ/4096:=by
    apply (div_le_iff₀ (show 0<10*(d:ℝ) by positivity)).2
    nlinarith [mul_nonneg hθ.le (show 0≤(d:ℝ)-1024 by linarith)]
  have ha:a≤θ/4096:=(min_le_left _ _).trans hbound
  have hg:γ≤θ/4096:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans hbound))
  exact max_le ha hg
end Oberwolfach
