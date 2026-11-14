module

public import Mathlib.Tactic

@[expose] public section
/-! A late local rate meets the summed-loss and transfer margins while the
global matching error remains independently fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_inner_sum_rate_choice
    (ε c rho eta cap:ℝ) (hε:0<ε) (hc:0<c) (hrho:0<rho) (heta:0<eta) (hcap:0<cap):
    ∃t:ℝ,0<t ∧ t≤cap ∧ 5*t≤ε*eta/2 ∧ 5*t≤c*rho*ε/8 ∧
      (17+2/rho)*t≤c*ε/4 :=by
  let t:=min (cap/2) (min (ε*eta/20) (min (c*rho*ε/80) (c*ε/(8*(17+2/rho)))))
  have hf:0<17+2/rho:=by positivity
  have ht:0<t:=by dsimp [t];positivity
  have h1:t≤cap/2:=min_le_left _ _
  have h2:t≤ε*eta/20:=(min_le_right _ _).trans (min_le_left _ _)
  have h3:t≤c*rho*ε/80:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4:t≤c*ε/(8*(17+2/rho)):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmul:=mul_le_mul_of_nonneg_left h4 hf.le
  have heq:(17+2/rho)*(c*ε/(8*(17+2/rho)))=c*ε/8:=by field_simp
  rw [heq] at hmul
  exact ⟨t,ht,by linarith,by linarith,by linarith,by have hp:0≤c*ε:=mul_nonneg hc.le hε.le; nlinarith⟩
end Oberwolfach
