module

public import Oberwolfach.OrdinaryEndpointRimRelativeProfiles
public import Oberwolfach.OrdinaryCleanupSpokeCodegrees

@[expose] public section
/-! The actual endpoint classes have linear size whenever the sampled means
    dominate the stated edit and concentration errors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_endpoint_sizes_from_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH L βe βh a:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH L βe βh s j σ)
    (hRbudget:a*Fintype.card (V⊕U)+tR+L≤pR*density*A.card)
    (hHbudget:a*Fintype.card (V⊕U)+tH+L≤pH*B.card):
    (∀x,a*Fintype.card (V⊕U)≤((A∩Q.neighborFinset x).card:ℝ)) ∧
    (∀x,a*Fintype.card (V⊕U)≤((B.filter (H x)).card:ℝ)):=by
  have hrim:=ordinary_endpoint_rim_relative_profiles P Q F H A B π d j s pR pH density tR tH L βe βh σ profile
  have hspoke:=ordinary_cleanup_spoke_degrees_and_codegrees P Q F H π d A B pR pH density tR tH L βe βh s j σ profile
  constructor
  · intro x
    have hh:=mul_le_mul_of_nonneg_left (profile.parent_min_degree x) profile.rim_nonneg
    have hl:=(abs_le.mp (hrim.1 x)).1
    nlinarith only [hh,hl,hRbudget]
  · intro x
    have hl:=(abs_le.mp (hspoke.1 x)).1
    linarith only [hl,hHbudget]
end Oberwolfach
