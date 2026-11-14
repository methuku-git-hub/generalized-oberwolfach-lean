module

public import Oberwolfach.OrdinaryCleanupParentProfiles

@[expose] public section
/-! The common raw sample and cleanup profile imply the parent extension
counts required for the fresh boundary reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_parent_extensions_from_profile
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH L βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH L βe βh s j σ) :
    ∀a c u,βe*Fintype.card (V⊕U)≤((A.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u)).card:ℝ) := by
  have hcommon:=ordinary_boundary_parent_common_of_min_degree P A density profile.parent_min_degree
  exact ordinary_boundary_parent_extensions_from_common_sample P Q H π d A pR pH (2*density-1)
    tR L βe profile.rim_nonneg profile.rim_le_one profile.spoke_nonneg (by linarith [profile.density_large])
    s j σ profile.spoke_probability profile.rows hcommon profile.rim_edit profile.spoke_column_edit profile.extension_margin
end Oberwolfach
