module

public import Oberwolfach.OrdinaryOriginalJointCorrectionPlacementChoices
public import Oberwolfach.OrdinaryOriginalPreSampleFromJoint

@[expose] public section
/-! Under the original positive margins, choose correction geometry, the
matching and placement parameters, and one edit rate before absorber sizes,
failure probabilities, the factors and the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach

theorem ordinary_original_presample_correction_choices
    (L rstar:ℕ) (βfreq ρ₀ α εmax capEdit θhost:ℝ)
    (hr:3 ≤ rstar) (hβ:0<βfreq) (hβ1:βfreq ≤ 1) (hρ:0<ρ₀) (hρ1:ρ₀ ≤ 1)
    (hα:0<α) (hεmax:0<εmax) (hcap:0<capEdit) (hθhost:1/2 ≤ θhost):
    let smin:=βfreq/200;let pstar:=ρ₀*smin/2;let ω:=ρ₀/4;
    ∃δAbs h εabs εv:ℝ,
      OrdinaryWeightedCorrectionAfterEarly rstar (α/2) pstar ω δAbs h εabs εv ∧
      let capInner:=min εmax (min εabs εv);
      0<capInner ∧ capInner ≤ εmax ∧ capInner ≤ εabs ∧ capInner ≤ εv ∧
      OrdinaryOriginalPreSampleJointShape L rstar βfreq ρ₀ α (α/2) capInner capEdit θhost
        hr hβ hβ1 hρ hα :=by
  intro smin pstar ω
  obtain ⟨δAbs,h,εabs,εv,hCorr,hInner,hMax,hAbs,hV,hJoint⟩:=
    ordinary_original_joint_correction_placement_choices L rstar βfreq ρ₀ α εmax capEdit θhost
      hr hβ hβ1 hρ hρ1 hα hεmax hcap hθhost
  have hPre:=ordinary_original_presample_from_joint L rstar βfreq ρ₀ α (α/2)
    (min εmax (min εabs εv)) capEdit θhost hr hβ hβ1 hρ hα hJoint
  exact ⟨δAbs,h,εabs,εv,hCorr,hInner,hMax,hAbs,hV,hPre⟩
end Oberwolfach
