module

public import Oberwolfach.ApproximatePreparationTargetArithmetic

@[expose] public section
/-! The ordinary-rim balance follows by summing the actual hub identities,
with one term for each retained ordinary length. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem preparation_ordinary_rim_balance {U I:Type} [Fintype U] [Fintype I]
    (D p k m:ℝ) (hD:0<D) (hp:0<p)
    (q s:U→ℝ) (η:I→U→ℝ)
    (hbal:∀ u,m*q u+(∑ i,η i u)*s u=s u)
    (hq:(∑ u,q u)=D*k) (hs:(∑ u,s u)=D*p):
    m*k/p+(∑ i,(∑ u,η i u*s u)/(D*p))=1:=by
  have hsum:(∑ i,∑ u,η i u*s u)=D*p-m*(D*k):=by
    calc
      _ = ∑ u,(∑ i,η i u)*s u:=by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
      _ = ∑ u,(s u-m*q u):=by
        apply Finset.sum_congr rfl
        intro u _
        linarith [hbal u]
      _ = _:=by rw [Finset.sum_sub_distrib,← Finset.mul_sum,hq,hs]
  rw [← Finset.sum_div,hsum]
  field_simp
  <;> ring
end Oberwolfach
