module

public import Oberwolfach.FiniteLawSupportProbabilityMono

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_probability_reorder_uniform_event
    {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (Good Every Uniform:Ω→Prop) (b:ℝ)
    (h:b≤μ.probability (fun z=>Good z ∧ Every z ∧ Uniform z)):
    b≤μ.probability (fun z=>(Good z ∧ Uniform z) ∧ Every z) := by
  apply h.trans
  apply finiteLaw_probability_mono_on_support
  intro z hz h
  exact ⟨⟨h.1,h.2.2⟩,h.2.1⟩
end Oberwolfach
