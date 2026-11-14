module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
/-! The original marked and ordinary coefficient profiles add to one at
each ordinary spoke and at each ordinary physical rim. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_approximate_spoke_coefficients_sum_one {U I:Type} [Fintype I]
    (m:ℕ) (a b:U→ℝ) (f:I→U→ℝ)
    (hb:∀u,0<b u) (hbalance:∀u,b u=(m:ℝ)*a u+∑i,f i u):
    ∀u,(m:ℝ)*a u/b u+∑i,f i u/b u=1:=by
  intro u
  rw [←Finset.sum_div,←add_div,←hbalance]
  exact div_self (ne_of_gt (hb u))

theorem long_approximate_ordinary_rim_coefficients_sum_one {U I:Type} [Fintype U] [Fintype I]
    (m:ℕ) (D p k:ℝ) (hD:0<D) (hp:0<p)
    (a b:U→ℝ) (f:I→U→ℝ)
    (hbalance:∀u,b u=(m:ℝ)*a u+∑i,f i u)
    (hpdef:p=(∑u,b u)/D) (hkdef:k=(∑u,a u)/D):
    (m:ℝ)*k/p+∑i,(∑u,f i u)/(D*p)=1:=by
  have hsum:(∑u,b u)=(m:ℝ)*(∑u,a u)+∑i,∑u,f i u:=by
    simp_rw [hbalance]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_comm]
  rw [←Finset.sum_div]
  have hpD:D*p=∑u,b u:=by rw [hpdef];field_simp
  have hkD:D*k=∑u,a u:=by rw [hkdef];field_simp
  have hfirst:(m:ℝ)*k/p=((m:ℝ)*(D*k))/(D*p):=by field_simp
  rw [hfirst,←add_div]
  have hden:0<D*p:=mul_pos hD hp
  apply (div_eq_one_iff_eq (ne_of_gt hden)).mpr
  nlinarith [hsum,hpD,hkD]
end Oberwolfach
