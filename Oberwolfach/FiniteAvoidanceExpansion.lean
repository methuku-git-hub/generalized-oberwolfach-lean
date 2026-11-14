module

public import Oberwolfach.FiniteCoordinateEvents
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Inclusion-exclusion for finite laws, also with an additional event.
The estimate compares joint probabilities, without asserting independence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_avoidance_indicator {J : Type*} (S : Finset J) (P : J → Prop) :
    (if ∀ j∈S,¬P j then (1 : ℝ) else 0)=
      ∑ T∈S.powerset,(-1 : ℝ)^T.card*(if ∀ j∈T,P j then 1 else 0) := by
  classical
  have he (j : J) : (if ¬P j then (1 : ℝ) else 0)=1-(if P j then 1 else 0) := by
    by_cases h : P j <;> simp [h]
  rw [← Finset.prod_boole]
  simp_rw [he]
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one,mul_one,Finset.prod_boole]

theorem finiteLaw_avoidance_expansion {Ω J : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (S : Finset J) (A : J → Ω → Prop) (P : Ω → Prop) :
    μ.probability (fun ω=>P ω ∧ ∀ j∈S,¬A j ω)=
      ∑ T∈S.powerset,(-1 : ℝ)^T.card*
        μ.probability (fun ω=>P ω ∧ ∀ j∈T,A j ω) := by
  classical
  have he (ω : Ω) :
      (if P ω ∧ ∀ j∈S,¬A j ω then (1 : ℝ) else 0)=
        ∑ T∈S.powerset,(-1 : ℝ)^T.card*
          (if P ω ∧ ∀ j∈T,A j ω then 1 else 0) := by
    by_cases hp : P ω
    · simp only [hp,true_and]
      exact finite_avoidance_indicator S (fun j=>A j ω)
    · simp [hp]
  rw [finiteLaw_probability_eq_expectation]
  simp_rw [he]
  unfold FiniteLaw.expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  unfold FiniteLaw.probability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hp : P ω ∧ ∀ j∈T,A j ω <;> simp [hp,mul_comm,mul_left_comm]

theorem finiteLaw_avoidance_approximation {Ω J : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (S : Finset J) (A : J → Ω → Prop) (P : Ω → Prop)
    (p : ℝ) (r : J → ℝ) (ε : Finset J → ℝ)
    (h : ∀ T∈S.powerset,
      |μ.probability (fun ω=>P ω ∧ ∀ j∈T,A j ω)-p*(∏ j∈T,r j)|≤ε T) :
    |μ.probability (fun ω=>P ω ∧ ∀ j∈S,¬A j ω)-p*(∏ j∈S,(1-r j))|≤
      ∑ T∈S.powerset,ε T := by
  classical
  have hprod : (∏ j∈S,(1-r j))=∑ T∈S.powerset,(-1 : ℝ)^T.card*(∏ j∈T,r j) := by
    rw [Finset.prod_sub]
    simp only [Finset.prod_const_one,mul_one]
  rw [finiteLaw_avoidance_expansion,hprod,Finset.mul_sum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ T∈S.powerset,|(-1 : ℝ)^T.card*
        μ.probability (fun ω=>P ω ∧ ∀ j∈T,A j ω)-p*((-1)^T.card*(∏ j∈T,r j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ T∈S.powerset,
        |μ.probability (fun ω=>P ω ∧ ∀ j∈T,A j ω)-p*(∏ j∈T,r j)| := by
      apply Finset.sum_congr rfl
      intro T _
      rw [show (-1 : ℝ)^T.card*μ.probability (fun ω=>P ω ∧ ∀ j∈T,A j ω)-
        p*((-1)^T.card*(∏ j∈T,r j))=
        (-1)^T.card*(μ.probability (fun ω=>P ω ∧ ∀ j∈T,A j ω)-p*(∏ j∈T,r j)) by ring]
      simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    _ ≤ _ := Finset.sum_le_sum h

end Oberwolfach
