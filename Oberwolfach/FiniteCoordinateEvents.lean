module

public import Oberwolfach.FiniteExponential
public import Oberwolfach.CommonEvents

@[expose] public section

/-! Exact probabilities of coordinatewise conditions under a finite
product law, including complementary one-point conditions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_probability_point
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (a : Ω) :
    μ.probability (fun x=>x=a)=μ.mass a := by
  classical
  unfold FiniteLaw.probability
  simp

theorem finiteLaw_probability_not_point
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (a : Ω) :
    μ.probability (fun x=>x≠a)=1-μ.mass a := by
  have hh := finiteLaw_probability_compl μ (fun x=>x=a)
  rw [finiteLaw_probability_point] at hh
  linarith

theorem finiteLaw_probability_true
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) :
    μ.probability (fun _=>True)=1 := by
  unfold FiniteLaw.probability
  simp only [ite_true]
  exact μ.total

theorem finiteLaw_pi_probability_forall
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i,Fintype (Ω i)]
    (μ : ∀ i,FiniteLaw (Ω i)) (A : ∀ i,Ω i → Prop) :
    (FiniteLaw.pi μ).probability (fun x=>∀ i,A i (x i))=
      ∏ i,(μ i).probability (A i) := by
  classical
  have he (x : ∀ i,Ω i) :
      (if ∀ i,A i (x i) then (1 : ℝ) else 0)=
        ∏ i,if A i (x i) then (1 : ℝ) else 0 := by
    by_cases h : ∀ i,A i (x i)
    · simp [h]
    · rw [if_neg h]
      obtain ⟨i,hi⟩ := not_forall.mp h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi,ite_false])
  rw [finiteLaw_probability_eq_expectation]
  simp_rw [he]
  rw [finiteLaw_pi_expectation_product μ (fun i a=>if A i a then (1 : ℝ) else 0)]
  apply Finset.prod_congr rfl
  intro i _
  exact (finiteLaw_probability_eq_expectation (μ i) (A i)).symm

theorem finiteLaw_probability_value_partition
    {Ω C : Type*} [Fintype Ω] [Fintype C]
    (μ : FiniteLaw Ω) (A : Ω → Prop) (f : Ω → C) :
    μ.probability A=∑ c,μ.probability (fun x=>A x ∧ f x=c) := by
  classical
  unfold FiniteLaw.probability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : A x
  · simp [hx]
  · simp [hx]

theorem finiteLaw_expectation_count
    {Ω J : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (T : Finset J) (A : J → Ω → Prop) :
    μ.expectation (fun x=>((T.filter (fun j=>A j x)).card : ℝ))=
      ∑ j∈T,μ.probability (A j) := by
  classical
  unfold FiniteLaw.expectation FiniteLaw.probability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  rw [← Finset.sum_boole (fun j=>A j x) T,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : A j x <;> simp [h]

end Oberwolfach
