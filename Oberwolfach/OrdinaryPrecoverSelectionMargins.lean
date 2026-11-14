module

public import Oberwolfach.OrdinaryGeneralSelectionMarginsFromCleanup

@[expose] public section
/-! The pre-cover selection inequalities follow from the existing cleanup
hierarchy by charging the larger of the two cover-degree scales. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U]

theorem ordinary_precover_selection_margins
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (Z:Finset U)
    (pR pH density tR tH Ledit βe βh κ ζ p ε t ν η ell:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe βh s j raw)
    (hX:X.Nonempty) (hκscale:κ*Fintype.card V≤βe*Fintype.card (V⊕U))
    (hκ:0<κ) (hζ:0<ζ) (hp:0<p) (hp1:p≤1) (hu:Fintype.card U≤Fintype.card V)
    (hη:0≤η) (hell:0≤ell) (hε:ε≤p^2/4)
    (hsmall:t+(ν+max η ell)≤(p^2/4)*Fintype.card (V⊕U))
    (hpκ:p≤4*ζ*min (κ/2) 1) (hsqrt:20*Real.sqrt (2*p)≤ζ*min (κ/2) 1/2)
    (hν:ν+max η ell≤ζ*min (κ/2) 1*p*Fintype.card (V⊕U)/4)
    (horder:2≤ζ*min (κ/2) 1*p*Fintype.card (V⊕U)/4):
    (p+ε)*Fintype.card (V⊕U)+(t+ν)≤(2*p)*Fintype.card (V⊕U) ∧
    (p^2+ε)*Fintype.card (V⊕U)+2*(t+ν)≤(2*p)^2*Fintype.card (V⊕U) ∧
    (∀j:{u:U // u∉Z},t+ν+ell≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card)) ∧
    t+ν+ell≤ζ*(p*Fintype.card (V⊕U)) ∧
    (∀j:{u:U // u∉Z},2*((2*p)*Real.sqrt (2*p)*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*((2*p)*Real.sqrt (2*p)*Fintype.card (V⊕U))):ℝ)+(ν+η)≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card)) ∧
    2*((2*p)*Real.sqrt (2*p)*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*((2*p)*Real.sqrt (2*p)*Fintype.card (V⊕U))):ℝ)+(ν+η)≤ζ*(p*Fintype.card (V⊕U)):=by
  have hm:=ordinary_general_selection_margins_from_cleanup P Q F H π d X Z pR pH density tR tH Ledit βe βh
    κ ζ p ε t (ν+max η ell) s j raw profile hX hκscale hκ hζ hp hp1 hu hε hsmall hpκ hsqrt hν horder
  have hmax0:0≤max η ell:=le_trans hη (le_max_left _ _)
  have hmaxη:η≤max η ell:=le_max_left _ _
  have hmaxell:ell≤max η ell:=le_max_right _ _
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · linarith only [hm.1,hmax0]
  · linarith only [hm.2.1,hmax0]
  · intro j
    have hh:=hm.2.2.1 j
    linarith only [hh,hmaxell]
  · linarith only [hm.2.2.2.1,hmaxell]
  · intro j
    have hh:=hm.2.2.2.2.1 j
    linarith only [hh,hmaxη]
  · linarith only [hm.2.2.2.2.2,hmaxη]
end Oberwolfach
