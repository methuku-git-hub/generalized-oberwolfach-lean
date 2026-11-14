module

public import Oberwolfach.MarkedSeedNormalization

@[expose] public section
/-! Algebra of the prescribed heterogeneous hub marginals in the
root-omitted preparation targets. No sampling or candidate identity is
assumed or asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem approximate_preparation_target_arithmetic
    {U R:Type} [Fintype U] [Fintype R]
    (D p k m:ℝ) (hD:0<D) (hp:0<p) (hk:0<k)
    (a b:U→ℝ) (η:U→R→ℝ) (hb:∀ u,0<b u)
    (hbal:∀ u,m*a u+(∑ r,η u r)*b u=b u)
    (ha:(∑ u,a u)=D*k) (hbs:(∑ u,b u)=D*p):
    (∀ u,m*a u/b u+∑ r,η u r=1) ∧
    (∑ u,a u)/(D*k)=1 ∧
    m*k/p+(∑ u,(b u-m*a u))/(D*p)=1:=by
  constructor
  · intro u
    have hbn:b u≠0:=ne_of_gt (hb u)
    field_simp
    nlinarith [hbal u]
  constructor
  · rw [ha]
    exact div_self (ne_of_gt (mul_pos hD hk))
  · have hs:(∑ u,(b u-m*a u))=D*p-m*(D*k):=by
      rw [Finset.sum_sub_distrib,← Finset.mul_sum,ha,hbs]
    rw [hs]
    field_simp
    ring
end Oberwolfach
