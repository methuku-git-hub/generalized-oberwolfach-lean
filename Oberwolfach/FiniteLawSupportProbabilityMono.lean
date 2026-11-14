module

public import Oberwolfach.FiniteLawSupportAlmostSure
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Deterministic consequences valid on the support preserve a probability
lower bound, even when the finite sample space has zero-mass outcomes. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_probability_mono_on_support {Ω:Type} [Fintype Ω]
    (μ:FiniteLaw Ω) (A B:Ω→Prop) (h:∀z,0<μ.mass z→A z→B z):
    μ.probability A≤μ.probability B := by
  rw [←finiteLaw_support_probability μ A,←finiteLaw_support_probability μ B]
  apply finiteLaw_probability_mono
  intro z hz
  exact h z.val z.property hz
end Oberwolfach
