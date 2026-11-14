module

public import Oberwolfach.OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent
public import Oberwolfach.OrdinaryAdaptiveHubWeightsLevelEvent

@[expose] public section
/-! The stronger inner-scale weight event supplies the earlier ambient
interface without changing its selected cycles or weighted loads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def ordinary_inner_hub_weights_ambient_transfer
    (m:ℕ) (b Binner Bambient η K:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (hA:0<A.card) (hb:0≤b) (hB:0≤Binner) (hK:0≤K)
    (hsize:(Fintype.card V:ℝ)≤K*A.card) (hBambient:Binner*K^m≤Bambient)
    (data:OrdinaryMixedHubWeightsInnerScale m b Binner η Q F H A Z):
    OrdinaryMixedHubWeightsOfLength m b Bambient η Q F H A Z:=by
  refine ⟨data.weight,?_,data.loads⟩
  intro j C
  have ha:(0:ℝ)<A.card:=Nat.cast_pos.mpr hA
  have han:(A.card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ A
  have hh:=ordinary_weight_scale_transfer_power m A.card (Fintype.card V) b Binner K (data.weight j C)
    ha han hK hsize hb hB (data.bounds j C).1 (data.bounds j C).2
  exact ⟨hh.1,hh.2.trans (div_le_div_of_nonneg_right hBambient (by positivity))⟩

theorem ordinary_inner_hub_weight_event_ambient_transfer
    (m:ℕ) (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (d:ℕ)
    (pR pH density tR tH Ledit βe βh b Binner Bambient η K:ℝ) (s:U→Color→ℝ) (j:Color)
    (σ:RawWheelOutcome V U Γ Color)
    (hA:0<A.card) (hb:0≤b) (hB:0≤Binner) (hK:0≤K)
    (hsize:(Fintype.card V:ℝ)≤K*A.card) (hBambient:Binner*K^m≤Bambient)
    (event:OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent m P F A Z π d pR pH density tR tH Ledit βe βh b Binner η s j σ):
    OrdinaryAdaptiveHubWeightsLevelEvent m P F A Z π d pR pH density tR tH Ledit βe βh b Bambient η s j σ:=by
  intro Q H profile hQ
  obtain ⟨data⟩:=event Q H profile hQ
  exact ⟨ordinary_inner_hub_weights_ambient_transfer m b Binner Bambient η K Q F H A Z
    hA hb hB hK hsize hBambient data⟩
end Oberwolfach
