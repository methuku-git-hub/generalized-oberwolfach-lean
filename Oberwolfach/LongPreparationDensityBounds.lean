module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

@[expose] public section
/-! Lower bounds on the fixed approximate-state densities from the long
preparation's prescribed hub marginals. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_preparation_density_bounds {U:Type} [Fintype U]
    (D rho c:ℝ) (hD:0<D) (hrho:0<rho) (hc:0<c)
    (a b:U→ℝ) (ha:∀ u,1/(3*c)≤a u) (hb:∀ u,1/4≤b u)
    (hm:rho*D/2≤(Fintype.card U:ℝ)):
    rho/8≤(∑ u,b u)/D ∧ rho/(6*c)≤(∑ u,a u)/D:=by
  classical
  have hbs:(Fintype.card U:ℝ)/4≤∑ u,b u:=by
    have hh:∑ _u:U,(1/4:ℝ)≤∑ u,b u:=Finset.sum_le_sum (fun u _=>hb u)
    simpa [div_eq_mul_inv] using hh
  have has:(Fintype.card U:ℝ)/(3*c)≤∑ u,a u:=by
    have hh:∑ _u:U,(1/(3*c):ℝ)≤∑ u,a u:=Finset.sum_le_sum (fun u _=>ha u)
    simpa [div_eq_mul_inv] using hh
  constructor
  · apply (le_div_iff₀ hD).2
    nlinarith [hbs,hm]
  · apply (le_div_iff₀ hD).2
    have hden:0<3*c:=by positivity
    have hx:=div_le_div_of_nonneg_right hm hden.le
    have heq:(rho*D/2)/(3*c)=(rho/(6*c))*D:=by field_simp <;> ring
    rw [heq] at hx
    exact hx.trans has

theorem long_preparation_eta_bound {U R:Type} [Fintype R]
    (b:U→ℝ) (eta:U→R→ℝ) (hb:∀ u,0<b u ∧ b u≤1)
    (heta:∀ u r,0≤eta u r)
    (hbal:∀ u,(∑ r,eta u r)*b u≤b u):
    ∀ u r,eta u r≤1/b u:=by
  classical
  intro u r
  have he:eta u r≤∑ r,eta u r:=Finset.single_le_sum (fun r _=>heta u r) (Finset.mem_univ r)
  have hm:=mul_le_mul_of_nonneg_right he (hb u).1.le
  apply (le_div_iff₀ (hb u).1).2
  linarith [hbal u,(hb u).2,hm]
end Oberwolfach
