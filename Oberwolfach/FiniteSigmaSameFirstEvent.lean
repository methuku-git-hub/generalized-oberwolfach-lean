module

public import Oberwolfach.FiniteSigmaFirstMap

@[expose] public section
/-! A first-stage event has the same probability under any dependent
second-stage finite laws. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem finiteLaw_sigma_same_first_event
    {Ω:Type} [Fintype Ω] {F G:Ω→Type} [∀ω,Fintype (F ω)] [∀ω,Fintype (G ω)]
    (μ:FiniteLaw Ω) (ν:∀ω,FiniteLaw (F ω)) (κ:∀ω,FiniteLaw (G ω)) (E:Ω→Prop):
    (μ.sigma ν).probability (fun z=>E z.1)=(μ.sigma κ).probability (fun z=>E z.1):=by
  rw [finiteLaw_sigma_first_probability μ ν E,finiteLaw_sigma_first_probability μ κ E]
end Oberwolfach
