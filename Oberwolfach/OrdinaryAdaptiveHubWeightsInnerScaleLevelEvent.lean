module

public import Oberwolfach.OrdinaryAdaptiveHubWeightsInnerScaleRawProbability

@[expose] public section
/-! At one fixed level, every later host with the stated cleanup profile has
ordinary hub weights; the event is chosen before that host is exposed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent
    (m:ℕ) (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (d:ℕ)
    (pR pH density tR tH Ledit βe βh b Bweight η:ℝ) (s:U→Color→ℝ) (j:Color)
    (σ:RawWheelOutcome V U Γ Color):Prop:=
  ∀(Q:SimpleGraph V) (H:V→U→Prop),
    OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ→
    Q≤P→Nonempty (OrdinaryMixedHubWeightsInnerScale m b Bweight η Q F H A Z)
end Oberwolfach
