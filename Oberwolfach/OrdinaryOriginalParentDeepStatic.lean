module

public import Oberwolfach.OrdinaryOriginalParentReferenceStatic
public import Oberwolfach.OrdinaryParentReferenceDeepJointStaticAt

@[expose] public section
/-! Retain the initial static geometry in the original non-triangle parent
reference choices, before the matching spacing is selected. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_original_parent_deep_static
    (rstar loadK:ℕ) (hr:4≤rstar) (βfreq ρ₀ α ηP:ℝ)
    (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1) (hα:0<α) (hη:0<ηP)
    (hmargin:α/2≤1/2 ∧ max (1/2) (cycleThreshold rstar)+(α/2)/2≤1)
    (aDeep ρdeep θdeep ηProfile αcut:ℝ)
    (ha:0<aDeep) (hρdeep:0<ρdeep) (hθdeep:0<θdeep) (hprofile:0<ηProfile) (hcut:0<αcut)
    (ηcap gapcap ζlimit:ℝ) (hηcap:0<ηcap) (hgapcap:0<gapcap) (hζlimit:0<ζlimit):
    let pstar:=ρ₀*(βfreq/200)/2;
    OrdinaryParentReferenceDeepJointStaticAt (rstar-1) loadK (by omega) (α/2) ρ₀ pstar ηP (by positivity)
      aDeep ρdeep θdeep ηProfile αcut ηcap gapcap ζlimit :=by
  intro pstar
  have hchoices:=ordinary_original_parent_reference_static rstar loadK hr βfreq ρ₀ α ηP hβ hβ1 hρ hρ1 hα hη hmargin
  exact ordinary_parent_reference_deep_joint_static_at (rstar-1) loadK (by omega) (α/2) ρ₀ pstar ηP (by positivity) hρ
    aDeep ρdeep θdeep ηProfile αcut ha hρdeep hθdeep hprofile hcut ηcap gapcap ζlimit hηcap hgapcap hζlimit hchoices
end Oberwolfach
