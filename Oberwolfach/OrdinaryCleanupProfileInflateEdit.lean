module

public import Oberwolfach.OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent

@[expose] public section
/-! A pre-sampled adaptive event can use an upper edit envelope. Later
profiles fit that envelope when their boundary margins have the stated slack. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_cleanup_profile_inflate_edit
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (Z:Finset U)
    (pR pH density tR tH Lold Lnew βeOld βhOld βeNew βhNew:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Lold βeOld βhOld s j raw)
    (hL:Lold≤Lnew)
    (hE:βeNew*Fintype.card (V⊕U)+3*Lnew≤βeOld*Fintype.card (V⊕U)+3*Lold)
    (hH:βhNew*Fintype.card (V⊕U)+2*Lnew≤βhOld*Fintype.card (V⊕U)+2*Lold):
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Lnew βeNew βhNew s j raw:=by
  refine ⟨profile.rim_nonneg,profile.rim_le_one,profile.spoke_nonneg,profile.density_large,
    profile.spoke_probability,profile.forbidden_disjoint,profile.parent_min_degree,profile.rows,profile.columns,
    (fun v=>(profile.rim_edit v).trans hL),
    (fun u=>(profile.spoke_column_edit u).trans hL),
    (fun v=>(profile.spoke_row_edit v).trans hL),?_,?_⟩
  · linarith only [profile.extension_margin,hE]
  · linarith only [profile.hub_margin,hH]

theorem ordinary_adaptive_inner_weights_from_edit_envelope
    (m:ℕ) (P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (pR pH density tR tH Lold Lnew βeOld βhOld βeNew βhNew b B η:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (event:OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent m P F X Z π d pR pH density tR tH Lnew βeNew βhNew b B η s j raw)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Lold βeOld βhOld s j raw)
    (hQ:Q≤P) (hL:Lold≤Lnew)
    (hE:βeNew*Fintype.card (V⊕U)+3*Lnew≤βeOld*Fintype.card (V⊕U)+3*Lold)
    (hH:βhNew*Fintype.card (V⊕U)+2*Lnew≤βhOld*Fintype.card (V⊕U)+2*Lold):
    Nonempty (OrdinaryMixedHubWeightsInnerScale m b B η Q F H X Z):=by
  apply event Q H
  · exact ordinary_cleanup_profile_inflate_edit P Q F H π d X Z pR pH density tR tH Lold Lnew
      βeOld βhOld βeNew βhNew s j raw profile hL hE hH
  · exact hQ
end Oberwolfach
