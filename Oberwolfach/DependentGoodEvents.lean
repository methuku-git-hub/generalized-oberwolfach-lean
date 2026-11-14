module

public import Oberwolfach.TwoStageEvents

@[expose] public section

/-! An additive common-event bound for a first finite law followed by a
law depending on its outcome. The conditional bound is needed only on E. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem finiteLaw_twoStage_good {Ω : Type*} [Fintype Ω]
    {Γ : Ω→Type*} [∀ ω,Fintype (Γ ω)]
    (μ : FiniteLaw Ω) (ν : ∀ ω,FiniteLaw (Γ ω)) (E : Ω→Prop) (S : ∀ ω,Γ ω→Prop)
    (a b : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hE : 1-a≤μ.probability E) (hS : ∀ ω,E ω → 1-b≤(ν ω).probability (S ω)) :
    1-a-b≤(μ.sigma ν).probability (fun z=>E z.1 ∧ S z.1 z.2) := by
  by_cases hb1 : b≤1
  · have hh := finiteLaw_twoStage_survival μ ν E S b hS
    have hlo := mul_le_mul_of_nonneg_left hE (show 0≤1-b by linarith)
    have hab := mul_nonneg ha hb
    nlinarith only [hh,hlo,hab]
  · exact (by linarith : 1-a-b≤0).trans (finiteLaw_probability_nonneg _ _)

end Oberwolfach
