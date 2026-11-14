module

public import Oberwolfach.ConditionalRealization
public import Oberwolfach.FiniteCoordinateEvents

@[expose] public section

/-! Conditioning finite laws on events. The weighted identities remain
valid at zero probability, using the existing conditionOnMap convention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FiniteLaw.conditionEvent {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Prop) : FiniteLaw Ω :=
  μ.conditionOnMap (fun x=>decide (A x)) true

theorem finiteLaw_boolean_event_mass {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Prop) :
    (μ.map (fun x=>decide (A x))).mass true=μ.probability A := by
  unfold FiniteLaw.map FiniteLaw.probability
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : A x <;> simp [h]

theorem finiteLaw_conditionEvent_weight {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Prop) (x : Ω) :
    μ.probability A*(μ.conditionEvent A).mass x=if A x then μ.mass x else 0 := by
  have h := finiteLaw_conditionOnMap_weight μ (fun x=>decide (A x)) true x
  rw [finiteLaw_boolean_event_mass] at h
  simpa only [FiniteLaw.conditionEvent,decide_eq_true_eq] using h

theorem finiteLaw_conditionEvent_probability {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A B : Ω → Prop) :
    μ.probability A*(μ.conditionEvent A).probability B=μ.probability (fun x=>A x ∧ B x) := by
  unfold FiniteLaw.probability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hb : B x
  · simp only [hb,ite_true,and_true]
    exact finiteLaw_conditionEvent_weight μ A x
  · simp [hb]

theorem finiteLaw_pi_conditionEvent_probability
    {I : Type*} [Fintype I] {Ω : I → Type*} [∀ i,Fintype (Ω i)]
    (μ : ∀ i,FiniteLaw (Ω i)) (A : ∀ i,Ω i → Prop) (B : (∀ i,Ω i) → Prop) :
    (∏ i,(μ i).probability (A i))*
      (FiniteLaw.pi (fun i=>(μ i).conditionEvent (A i))).probability B=
        (FiniteLaw.pi μ).probability (fun x=>(∀ i,A i (x i)) ∧ B x) := by
  classical
  unfold FiniteLaw.probability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hb : B x
  · simp only [hb,ite_true,and_true,FiniteLaw.pi]
    rw [← Finset.prod_mul_distrib]
    have hcoord (i : I) := finiteLaw_conditionEvent_weight (μ i) (A i) (x i)
    simp only [FiniteLaw.probability] at hcoord
    simp_rw [hcoord]
    by_cases ha : ∀ i,A i (x i)
    · simp [ha]
    · rw [if_neg ha]
      obtain ⟨i,hi⟩ := not_forall.mp ha
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  · simp [hb]

end Oberwolfach
