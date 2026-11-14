module

public import Oberwolfach.FiniteLawSupportProbabilityMono
public import Oberwolfach.FiniteLawMap

@[expose] public section
/-! Project an event whose deterministic continuation is proved on the
support, retaining a uniform statement for every admissible later host. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_map_common_event_on_support
    {Ω Γ X Y:Type} [Fintype Ω] [Fintype Γ]
    (μ:FiniteLaw Ω) (f:Ω→Γ) (E:Ω→Prop)
    (admissible:Γ→X→Prop) (conclusion:Γ→X→Y→Prop)
    (hE:∀ω,0<μ.mass ω→E ω→∀x,admissible (f ω) x→∃y,conclusion (f ω) x y):
    μ.probability E≤(μ.map f).probability (fun γ=>∀x,admissible γ x→∃y,conclusion γ x y) := by
  rw [finiteLaw_map_probability]
  exact finiteLaw_probability_mono_on_support μ E _ hE
end Oberwolfach
