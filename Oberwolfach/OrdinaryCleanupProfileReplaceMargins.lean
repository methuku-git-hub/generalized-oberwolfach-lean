module

public import Oberwolfach.OrdinaryCleanupParentProfiles

@[expose] public section
/-! Preserve the same sampled parent and edit bounds while replacing its
    numerical extension margins by separately verified bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_cleanup_profile_replace_margins
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (Z:Finset U)
    (pR pH density tR tH L βe βh βe' βh':ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (h:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe βh s j raw)
    (he:βe'*Fintype.card (V⊕U)+tR+3*L≤pR^2*pH*(2*density-1)*X.card)
    (hh:βh'*Fintype.card (V⊕U)+tH+2*L≤pH^2*Z.card):
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe' βh' s j raw :=
  ⟨h.rim_nonneg,h.rim_le_one,h.spoke_nonneg,h.density_large,h.spoke_probability,h.forbidden_disjoint,
    h.parent_min_degree,h.rows,h.columns,h.rim_edit,h.spoke_column_edit,h.spoke_row_edit,he,hh⟩
end Oberwolfach
