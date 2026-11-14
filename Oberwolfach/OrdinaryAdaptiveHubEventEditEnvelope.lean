module

public import Oberwolfach.OrdinaryCleanupProfileInflateEdit

@[expose] public section
/-! One sampled envelope event supplies all later events whose actual
edits and margins fit the envelope. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_adaptive_hub_event_of_edit_envelope
    (m:ℕ) (P F:SimpleGraph V) (X:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (pR pH density tR tH Lold Lnew βeOld βhOld βeNew βhNew b B η:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (event:OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent m P F X Z π d pR pH density tR tH Lnew βeNew βhNew b B η s j raw)
    (hL:Lold≤Lnew)
    (hE:βeNew*Fintype.card (V⊕U)+3*Lnew≤βeOld*Fintype.card (V⊕U)+3*Lold)
    (hH:βhNew*Fintype.card (V⊕U)+2*Lnew≤βhOld*Fintype.card (V⊕U)+2*Lold):
    OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent m P F X Z π d pR pH density tR tH Lold βeOld βhOld b B η s j raw:=by
  intro Q H profile hQ
  exact ordinary_adaptive_inner_weights_from_edit_envelope m P Q F H X Z π d pR pH density tR tH
    Lold Lnew βeOld βhOld βeNew βhNew b B η s j raw event profile hQ hL hE hH
end Oberwolfach
