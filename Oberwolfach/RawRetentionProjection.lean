module

public import Oberwolfach.RawUniformRetention
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! Retention keeps the original raw outcome as its first coordinate.
Any common raw event can therefore be joined with the retention event
without an independence assertion or re-exposure of the raw variables. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_sigma_first_probability {Ω : Type*} [Fintype Ω]
    {Γ : Ω→Type*} [∀ ω,Fintype (Γ ω)] (μ : FiniteLaw Ω) (ν : ∀ ω,FiniteLaw (Γ ω))
    (E : Ω→Prop) : (μ.sigma ν).probability (fun z=>E z.1)=μ.probability E := by
  rw [finiteLaw_sigma_probability]
  unfold FiniteLaw.expectation FiniteLaw.probability
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω
  · simp only [h,ite_true,(ν ω).total,mul_one]
  · simp only [h,ite_false,Finset.sum_const_zero,mul_zero]

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [Nonempty V] [DecidableEq V] [DecidableEq U]

theorem rawUniformRetentionLaw_projection (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d) (g : Γ)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (E : RawIntervalFamilyOutcome V U Γ Color→Prop) :
    (rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability (fun z=>E z.1)=
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E :=
  finiteLaw_sigma_first_probability _ _ E

theorem rawUniformRetentionLaw_common_event (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d) (g : Γ)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (E : RawIntervalFamilyOutcome V U Γ Color→Prop)
    (Good : RawRetainedIntervalOutcome (U:=U) (Color:=Color) π d g→Prop) (a b : ℝ)
    (hE : 1-a≤(FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E)
    (hG : 1-b≤(rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability Good) :
    1-a-b≤(rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability (fun z=>E z.1 ∧ Good z) := by
  have he := rawUniformRetentionLaw_projection π d hd g q hq hQ s hs hS E
  rw [← he] at hE
  exact (sub_le_sub_right hE b).trans (finiteLaw_good_intersection _ (fun z=>E z.1) Good b hG)

end Oberwolfach
