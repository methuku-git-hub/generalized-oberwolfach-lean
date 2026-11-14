module

public import Oberwolfach.OrdinaryGeneralSelectionMarginsFromSizes
public import Oberwolfach.OrdinaryGeneralHubConditionsFromCleanup

@[expose] public section
/-! The actual hub class size lower bounds and ordered small-density margins
supply all the selection inequalities for the general-length boundary finish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U]

theorem ordinary_general_selection_margins_from_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (Z:Finset U)
    (pR pH density tR tH Ledit βe βh κ ζ p ε t ν:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe βh s j raw)
    (hX:X.Nonempty) (hκscale:κ*Fintype.card V≤βe*Fintype.card (V⊕U))
    (hκ:0<κ) (hζ:0<ζ) (hp:0<p) (hp1:p≤1)
    (hu:Fintype.card U≤Fintype.card V)
    (hε:ε≤p^2/4) (hsmall:t+ν≤(p^2/4)*Fintype.card (V⊕U))
    (hpκ:p≤4*ζ*min (κ/2) 1)
    (hsqrt:20*Real.sqrt (2*p)≤ζ*min (κ/2) 1/2)
    (hν:ν≤ζ*min (κ/2) 1*p*Fintype.card (V⊕U)/4)
    (horder:2≤ζ*min (κ/2) 1*p*Fintype.card (V⊕U)/4):
    (p+ε)*Fintype.card (V⊕U)+(t+ν)≤(2*p)*Fintype.card (V⊕U) ∧
    (p^2+ε)*Fintype.card (V⊕U)+2*(t+ν)≤(2*p)^2*Fintype.card (V⊕U) ∧
    (∀j:{u:U // u∉Z},t+ν≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card)) ∧
    (t+ν≤ζ*(p*Fintype.card (V⊕U))) ∧
    (∀j:{u:U // u∉Z},2*((2*p)*Real.sqrt (2*p)*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*((2*p)*Real.sqrt (2*p)*Fintype.card (V⊕U))):ℝ)+ν≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card)) ∧
    (2*((2*p)*Real.sqrt (2*p)*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*((2*p)*Real.sqrt (2*p)*Fintype.card (V⊕U))):ℝ)+ν≤ζ*(p*Fintype.card (V⊕U))):=by
  have hhub:=(ordinary_general_hub_conditions_from_cleanup P Q F H X Z π d j s κ κ pR pH density
    tR tH Ledit βe βh raw profile hX hκscale hκscale).1
  exact ordinary_general_selection_margins_from_sizes H X Z κ ζ p ε t ν hκ hζ hp hp1 hu hhub
    hε hsmall hpκ hsqrt hν horder
end Oberwolfach
