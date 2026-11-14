module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
/-! Algebraic normalization of the ideal mixed physical rim and spoke
loads with heterogeneous hub frequencies. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem ordinary_mixed_ideal_normalization {I U:Type} [Fintype I] [Fintype U]
    (m D p:ℝ) (hD:0<D) (hp:0<p)
    (a b:U→ℝ) (η:I→U→ℝ) (hb:∀u,0<b u)
    (hbal:∀u,m*a u+(∑i,η i u)*b u=b u)
    (hpdef:(∑u,(a u+b u))=D*p):
    (∀u,m*a u/b u+∑i,η i u=1) ∧
    (m+1)*(∑u,a u)/(D*p)+(∑i,∑u,η i u*b u)/(D*p)=1 :=by
  constructor
  · intro u
    have hh:=hbal u
    field_simp [ne_of_gt (hb u)]
    nlinarith
  · have htotal:(m+1)*(∑u,a u)+(∑i,∑u,η i u*b u)=∑u,(a u+b u):=by
      rw [Finset.mul_sum,Finset.sum_comm,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      rw [←Finset.sum_mul]
      have hh:=hbal u
      nlinarith
    rw [hpdef] at htotal
    field_simp
    nlinarith
end Oberwolfach
