module

public import Oberwolfach.FiniteLengthsByClass

@[expose] public section
/-! Aggregate the supplied additive frequency errors without changing their scale. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem class_frequency_domain_error {K:ℕ} (r count frac:Fin K→ℝ) (θ n eps:ℝ)
    (hr:∀i,0<r i)
    (h:∀i,|count i-(1-θ)*frac i*n/r i|≤eps*n):
    |(∑i,r i*count i)-(1-θ)*n*(∑i,frac i)| ≤ (eps*n)*(∑i,r i) :=by
  have hid:(∑i,r i*count i)-(1-θ)*n*(∑i,frac i)=
      ∑i,r i*(count i-(1-θ)*frac i*n/r i):=by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hz:r i≠0:=ne_of_gt (hr i)
    field_simp
    <;> ring
  rw [hid]
  calc
    |∑i,r i*(count i-(1-θ)*frac i*n/r i)| ≤
        ∑i,|r i*(count i-(1-θ)*frac i*n/r i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑i,r i*(eps*n):=by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul,abs_of_pos (hr i)]
      exact mul_le_mul_of_nonneg_left (h i) (le_of_lt (hr i))
    _ = (eps*n)*(∑i,r i):=by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i hi;ring
end Oberwolfach
