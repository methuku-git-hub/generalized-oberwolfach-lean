module

public import Oberwolfach.FiniteEventConditioning
public import Oberwolfach.FiniteLawL1

@[expose] public section

/-! Comparing an event measurable through coordinate maps before and after
coordinatewise conditioning. The probability of the conditioning event is
retained, including when it is zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_pi_map_probability
    {I Ω Γ : Type*} [Fintype I] [Fintype Ω] [Fintype Γ]
    (μ : I → FiniteLaw Ω) (f : I → Ω → Γ) (B : (I → Γ) → Prop) :
    (FiniteLaw.pi μ).probability (fun x=>B (fun i=>f i (x i)))=
      (FiniteLaw.pi (fun i=>(μ i).map (f i))).probability B := by
  rw [← finiteLaw_map_probability,finiteLaw_pi_map]

theorem finiteLaw_conditioned_map_covariance
    {I Ω Γ : Type*} [Fintype I] [Fintype Ω] [Fintype Γ]
    (μ : I → FiniteLaw Ω) (A : I → Ω → Prop)
    (f : I → Ω → Γ) (B : (I → Γ) → Prop) :
    |(FiniteLaw.pi μ).probability (fun x=>(∀ i,A i (x i)) ∧ B (fun i=>f i (x i)))-
      (FiniteLaw.pi μ).probability (fun x=>∀ i,A i (x i))*
        (FiniteLaw.pi μ).probability (fun x=>B (fun i=>f i (x i)))|≤
      (FiniteLaw.pi μ).probability (fun x=>∀ i,A i (x i))*
        ∑ i,((μ i).conditionEvent (A i) |>.map (f i)).l1Distance ((μ i).map (f i)) := by
  classical
  let ν := fun i=>(μ i).conditionEvent (A i)
  let q := (FiniteLaw.pi μ).probability (fun x=>∀ i,A i (x i))
  have hq : 0≤q := finiteLaw_probability_nonneg _ _
  have he := finiteLaw_pi_conditionEvent_probability μ A (fun x=>B (fun i=>f i (x i)))
  rw [← finiteLaw_pi_probability_forall μ A] at he
  rw [finiteLaw_pi_map_probability] at he
  rw [← he,finiteLaw_pi_map_probability μ f B]
  change |q*(FiniteLaw.pi (fun i=>(ν i).map (f i))).probability B-
      q*(FiniteLaw.pi (fun i=>(μ i).map (f i))).probability B|≤q*_
  rw [← mul_sub,abs_mul,abs_of_nonneg hq]
  apply mul_le_mul_of_nonneg_left _ hq
  exact (finiteLaw_probability_l1 _ _ B).trans
    (finiteLaw_l1_pi (fun i=>(ν i).map (f i)) (fun i=>(μ i).map (f i)))

end Oberwolfach
