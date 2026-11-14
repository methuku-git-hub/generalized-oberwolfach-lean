module

public import Oberwolfach.OrdinaryUniformInnerHubEvent
public import Oberwolfach.OrdinaryVortexUniformEditCostEvents

@[expose] public section
/-! The all-edit weight event in the joint sample is exactly the named inner
hub event used by the actual initial and later protected-host certificates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_uniform_edit_inner_event_iff
    (P:SimpleGraph V) (D mv:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (m d:ℕ) (pR pH cap βe βh b B η:ℝ) (density tR tH:ℕ→ℝ)
    (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color):
    OrdinaryUniformEditWeightEvents Q π hπ m d pR pH cap βe βh b B η density tR tH s j σ ↔
    OrdinaryUniformInnerHubEvent m P D mv d β ε Q π hπ pR pH βe βh b B η cap density tR tH s j σ := by
  rfl
end Oberwolfach
