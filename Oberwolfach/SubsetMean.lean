module

public import Oberwolfach.SubsetInclusion

@[expose] public section

/-! Exact means of intersections with a uniform fixed-size sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixedSubset_vertex_probability {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (hr : r ≤ Fintype.card V) (x : V) :
    (FiniteLaw.uniform (FixedSubset V r)).probability (fun S => x ∈ S.1) =
      (r : ℝ) / Fintype.card V := by
  simpa only [Finset.card_singleton, Nat.choose_one_right, Finset.singleton_subset_iff]
    using fixedSubset_joint_inclusion hr {x}

theorem fixedSubset_intersection_mean {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (hr : r ≤ Fintype.card V) (A : Finset V) :
    (FiniteLaw.uniform (FixedSubset V r)).expectation (fun S => ((A ∩ S.1).card : ℝ)) =
      (A.card : ℝ) * ((r : ℝ) / Fintype.card V) := by
  have hc (S : FixedSubset V r) : ((A ∩ S.1).card : ℝ) =
      ∑ x ∈ A, if x ∈ S.1 then (1 : ℝ) else 0 := by
    simp
  simp only [FiniteLaw.expectation, hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x ∈ A, (FiniteLaw.uniform (FixedSubset V r)).probability (fun S => x ∈ S.1) := by
      apply Finset.sum_congr rfl
      intro x _
      unfold FiniteLaw.probability
      apply Finset.sum_congr rfl
      intro S _
      by_cases h : x ∈ S.1 <;> simp [h]
    _ = _ := by simp only [fixedSubset_vertex_probability hr, Finset.sum_const, nsmul_eq_mul]

end Oberwolfach
