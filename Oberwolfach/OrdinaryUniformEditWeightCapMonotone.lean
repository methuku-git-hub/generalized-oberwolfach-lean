module

public import Oberwolfach.OrdinaryVortexUniformEditCostEvents

@[expose] public section
/-! A sample that controls all edits up to a cap also controls a smaller cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D mv:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε mv)
  (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)

theorem ordinary_uniform_edit_weight_cap_monotone
    (m d:ℕ) (pR pH capSmall capLarge βe βh b B η:ℝ) (density tR tH:ℕ→ℝ)
    (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hcap:capSmall≤capLarge)
    (h:OrdinaryUniformEditWeightEvents Q π hπ m d pR pH capLarge βe βh b B η density tR tH s j σ):
    OrdinaryUniformEditWeightEvents Q π hπ m d pR pH capSmall βe βh b B η density tR tH s j σ :=by
  intro i hi L hL hLcap
  apply h i hi L hL
  exact hLcap.trans (mul_le_mul_of_nonneg_right hcap (by positivity))
end Oberwolfach
