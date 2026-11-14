module

public import Oberwolfach.FiniteCombinedUnitLoad

@[expose] public section
/-! Sum family-wise load errors over the active typed roots in one physical
fiber. The total ideal mass is normalized only after all roots are combined. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_fiber_combined_unit_load {A I:Type} [Fintype I]
    (T:Finset A) (target actual:A→I→ℝ) (τ t:ℝ)
    (hsum:∑a∈T,∑i,target a i=1)
    (h:∀a∈T,∀i,|actual a i-target a i|≤t+τ*target a i):
    |(∑a∈T,∑i,actual a i)-1|≤(T.card:ℝ)*(Fintype.card I:ℝ)*t+τ:=by
  have hh:|(∑a∈T,∑i,actual a i)-(∑a∈T,∑i,target a i)|≤
      ∑a∈T,∑i,|actual a i-target a i|:=by
    rw [←Finset.sum_sub_distrib]
    calc
      _ ≤ ∑a∈T,|(∑i,actual a i)-(∑i,target a i)|:=Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑a∈T,∑i,|actual a i-target a i|:=by
        apply Finset.sum_le_sum
        intro a _
        rw [←Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
  have hu:(∑a∈T,∑i,|actual a i-target a i|)≤∑a∈T,∑i,(t+τ*target a i):=by
    apply Finset.sum_le_sum
    intro a ha
    exact Finset.sum_le_sum (fun i _=>h a ha i)
  have he:(∑a∈T,∑i,(t+τ*target a i))=(T.card:ℝ)*(Fintype.card I:ℝ)*t+τ:=by
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.mul_sum,hsum,mul_one]
    ring
  rw [hsum] at hh
  linarith
end Oberwolfach
