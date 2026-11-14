module

public import Oberwolfach.OrdinaryWeightedCorrectionAfterEarly
public import Oberwolfach.OrdinaryOriginalSelectorPlacementJointShape
public import Oberwolfach.OrdinaryAssignedCorrectionOriginalRateChoice

@[expose] public section
/-! Select correction geometry first, then the independent reserved-list
placement hierarchy and original weighted matching selector. All choices
precede the factor family and expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach

theorem ordinary_original_joint_correction_placement_choices
    (L rstar:ℕ) (βfreq ρ₀ α εmax capEdit θhost:ℝ)
    (hr:3 ≤ rstar) (hβ:0<βfreq) (hβ1:βfreq ≤ 1) (hρ:0<ρ₀) (hρ1:ρ₀ ≤ 1)
    (hα:0<α) (hεmax:0<εmax) (hcap:0<capEdit) (hθhost:1/2 ≤ θhost):
    let smin:=βfreq/200;let pstar:=ρ₀*smin/2;let ω:=ρ₀/4;
    ∃δAbs h εabs εv:ℝ,
      OrdinaryWeightedCorrectionAfterEarly rstar (α/2) pstar ω δAbs h εabs εv ∧
      let capInner:=min εmax (min εabs εv);
      0<capInner ∧ capInner ≤ εmax ∧ capInner ≤ εabs ∧ capInner ≤ εv ∧
      OrdinaryOriginalSelectorPlacementJointShape L rstar βfreq ρ₀ α (α/2) capInner capEdit θhost
        hr hβ hβ1 hρ hα :=by
  intro smin pstar ω
  obtain ⟨hsmin,hpstar,hpstar1,hω,_⟩:=ordinary_assigned_correction_original_rate_choice βfreq ρ₀ hβ hβ1 hρ hρ1
  obtain ⟨δAbs,h,εabs,εv,hδ,hδsmall,hh,hεabs,hεv,hcorrection⟩:=
    ordinary_weighted_selector_correction_unconditional_prior rstar hr (α/2) pstar ω (by positivity) hpstar hpstar1 hω
  have hCorr:OrdinaryWeightedCorrectionAfterEarly rstar (α/2) pstar ω δAbs h εabs εv:=
    ⟨hδ,hδsmall,hh,hεabs,hεv,hcorrection⟩
  let capInner:ℝ:=min εmax (min εabs εv)
  have hInner:0<capInner:=by dsimp [capInner];positivity
  have hMax:capInner ≤ εmax:=min_le_left _ _
  have hAbs:capInner ≤ εabs:=(min_le_right _ _).trans (min_le_left _ _)
  have hV:capInner ≤ εv:=(min_le_right _ _).trans (min_le_right _ _)
  have hJoint:OrdinaryOriginalSelectorPlacementJointShape L rstar βfreq ρ₀ α (α/2) capInner capEdit θhost
      hr hβ hβ1 hρ hα:=
    ordinary_original_selector_placement_joint_choices L rstar βfreq ρ₀ α (α/2) capInner capEdit θhost
      hr hβ hβ1 hρ hα (by positivity) hInner hcap hθhost
  exact ⟨δAbs,h,εabs,εv,hCorr,hInner,hMax,hAbs,hV,hJoint⟩
end Oberwolfach
