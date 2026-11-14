module

public import Oberwolfach.OrdinaryCleanupParentProfiles

@[expose] public section
/-! A predetermined edit cap can replace a smaller realized edit count when
both numerical cleanup margins are verified for the predetermined cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_cleanup_profile_enlarge_edit
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (X:Finset V) (Z:Finset U) (pR pH density tR tH L L' βe βh:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (h:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe βh s j raw)
    (hLL:L≤L')
    (he:βe*Fintype.card (V⊕U)+tR+3*L'≤pR^2*pH*(2*density-1)*X.card)
    (hh:βh*Fintype.card (V⊕U)+tH+2*L'≤pH^2*Z.card):
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L' βe βh s j raw := by
  exact { h with
    rim_edit := fun v=>(h.rim_edit v).trans hLL
    spoke_column_edit := fun u=>(h.spoke_column_edit u).trans hLL
    spoke_row_edit := fun v=>(h.spoke_row_edit v).trans hLL
    extension_margin := he
    hub_margin := hh }
end Oberwolfach
