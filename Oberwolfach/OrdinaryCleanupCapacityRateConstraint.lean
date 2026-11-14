module

public import Oberwolfach.OrdinaryGeneralDeepSafeCapacityRuleQuantitative

@[expose] public section
/-! A necessary constraint imposed by the existing cleanup capacity inequality.
This isolates the scale dependence; it does not assert that the inequality is satisfiable. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_cleanup_capacity_requires_rate
    (N p βe ν extra:ℝ) (hN:0<N) (hν:0≤ν) (hextra:0≤extra)
    (hcapacity:8*p*N+extra<(βe/4)*N-3*(ν*N)):
    32*p<βe :=by
  have hn:0≤ν*N:=mul_nonneg hν hN.le
  by_contra h
  have hh:0≤(32*p-βe)*N:=mul_nonneg (by linarith) hN.le
  nlinarith only [hcapacity,hextra,hn,hh]

theorem ordinary_cleanup_selected_linear_boundary_requires_rate
    (N p cBoundary ε ν extra:ℝ) (hN:0<N) (hν:0≤ν) (hextra:0≤extra)
    (hcapacity:8*p*N+extra<((cBoundary*ε/2)/4)*N-3*(ν*N)):
    p<cBoundary*ε/64 :=by
  have hh:=ordinary_cleanup_capacity_requires_rate N p (cBoundary*ε/2) ν extra hN hν hextra hcapacity
  linarith only [hh]

theorem ordinary_cleanup_fixed_rate_not_uniform_at_small_vortex_scale
    (p cBoundary εcap:ℝ) (hp:0<p) (hc:0<cBoundary) (hcap:0<εcap):
    ∃ε:ℝ,0<ε ∧ ε≤εcap ∧ ∀(N ν extra:ℝ),0<N→0≤ν→0≤extra→
      ¬(8*p*N+extra<((cBoundary*ε/2)/4)*N-3*(ν*N)) :=by
  let ε:ℝ:=min (εcap/2) (16*p/cBoundary)
  have hε:0<ε:=by dsimp [ε];positivity
  have hεcap:ε≤εcap:=by have h:=min_le_left (εcap/2) (16*p/cBoundary);dsimp [ε];linarith
  have hεbound:cBoundary*ε≤16*p:=by
    have h:=mul_le_mul_of_nonneg_left (min_le_right (εcap/2) (16*p/cBoundary)) hc.le
    dsimp [ε] at *
    have heq:cBoundary*(16*p/cBoundary)=16*p:=by field_simp
    rw [heq] at h
    exact h
  refine ⟨ε,hε,hεcap,?_⟩
  intro N ν extra hN hν hextra hcapacity
  have hh:=ordinary_cleanup_selected_linear_boundary_requires_rate N p cBoundary ε ν extra hN hν hextra hcapacity
  linarith only [hh,hεbound,hp]
theorem ordinary_cleanup_capacity_rule_actual_requires_rate
    (N Kcap Dmax m:ℕ) (p βe ν Lconf:ℝ) (hN:0<N) (hK:0<Kcap)
    (hν:0≤ν) (hL:0≤Lconf)
    (hcapacity:((N*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*N)+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/4)*N-3*(ν*N)):
    32*p<βe :=by
  let extra:ℝ:=((N*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+4*((Kcap+Dmax:ℕ):ℝ)+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax
  have hextra:0≤extra:=by dsimp [extra];positivity
  have hcapacity':8*p*(N:ℝ)+extra<(βe/4)*(N:ℝ)-3*(ν*(N:ℝ)):=by
    dsimp [extra]
    linarith only [hcapacity]
  exact ordinary_cleanup_capacity_requires_rate N p βe ν extra (by exact_mod_cast hN) hν hextra hcapacity'
end Oberwolfach
