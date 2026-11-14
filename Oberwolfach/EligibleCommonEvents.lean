module

public import Oberwolfach.FiniteCoordinateEvents
public import Oberwolfach.CommonEvents

@[expose] public section

/-! A weighted union bound over a fixed family of candidates. The loss
is governed by the number eligible in one outcome, rather than by the
number of all ambient labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_eligible_bad_probability {Ω J : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (tests : Finset J) (Eligible Bad : J → Ω → Prop)
    (L ε : ℝ) (hε : 0 ≤ ε)
    (hL : ∀ ω,((tests.filter (fun j => Eligible j ω)).card:ℝ) ≤ L)
    (h : ∀ j∈tests,μ.probability (fun ω => Eligible j ω ∧ Bad j ω) ≤
      ε*μ.probability (Eligible j)) :
    μ.probability (fun ω => ∃ j∈tests,Eligible j ω ∧ Bad j ω) ≤ ε*L := by
  have hsum : (∑ j∈tests,μ.probability (Eligible j)) ≤ L := by
    rw [← finiteLaw_expectation_count]
    exact (finiteLaw_expectation_mono μ _ _ hL).trans_eq (finiteLaw_expectation_const μ L)
  calc
    _ ≤ ∑ j∈tests,μ.probability (fun ω => Eligible j ω ∧ Bad j ω) := finiteLaw_union_bound _ _ _
    _ ≤ ∑ j∈tests,ε*μ.probability (Eligible j) := Finset.sum_le_sum h
    _ = ε*(∑ j∈tests,μ.probability (Eligible j)) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hε

theorem finiteLaw_eligible_common_event {Ω J : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (tests : Finset J) (Eligible Bad : J → Ω → Prop)
    (L ε : ℝ) (hε : 0 ≤ ε)
    (hL : ∀ ω,((tests.filter (fun j => Eligible j ω)).card:ℝ) ≤ L)
    (h : ∀ j∈tests,μ.probability (fun ω => Eligible j ω ∧ Bad j ω) ≤
      ε*μ.probability (Eligible j)) :
    1-ε*L ≤ μ.probability (fun ω => ∀ j∈tests,Eligible j ω → ¬Bad j ω) := by
  have hb := finiteLaw_eligible_bad_probability μ tests Eligible Bad L ε hε hL h
  have hc := finiteLaw_probability_compl μ (fun ω => ∃ j∈tests,Eligible j ω ∧ Bad j ω)
  simp only [not_exists,not_and] at hc
  linarith

end Oberwolfach
