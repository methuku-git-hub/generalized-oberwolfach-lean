module

public import Oberwolfach.LocalMatchingTestDefect

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem local_matching_test_mass_le_card
    {R C:Type} [Fintype C] [DecidableEq R] [DecidableEq C]
    (I:Finset R) (Q:C→Finset R) (weight:C→ℝ)
    (hdegree:∀r∈I,(∑c,if r∈Q c then weight c else 0)≤1):
    (∑c,weight c*((Q c∩I).card:ℝ))≤I.card:=by
  have heq:∀c,weight c*((Q c∩I).card:ℝ)=∑r∈I,if r∈Q c then weight c else 0:=by
    intro c
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul, Finset.filter_mem_eq_inter, Finset.inter_comm, mul_comm]
  calc
    (∑c,weight c*((Q c∩I).card:ℝ)) = ∑c,∑r∈I,if r∈Q c then weight c else 0 :=by simp only [heq]
    _ = ∑r∈I,∑c,if r∈Q c then weight c else 0 :=by rw [Finset.sum_comm]
    _ ≤ ∑_r∈I,(1:ℝ) := Finset.sum_le_sum (fun r hr=>hdegree r hr)
    _ = I.card := by simp
end Oberwolfach
