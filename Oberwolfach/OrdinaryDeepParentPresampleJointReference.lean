module

public import Oberwolfach.OrdinaryDeepParentPresampleSameSpacing
public import Oberwolfach.OrdinaryParentReferenceDeepJointAt
public import Oberwolfach.OrdinaryPresampleParentSameSpacing
public import Oberwolfach.OrdinaryOriginalParentReferenceCompatible
public import Oberwolfach.OrdinaryOriginalPreSampleCorrectionChoices

@[expose] public section
/-! For reserved cycles of length at least four, select the deep wheel
constants before the ordinary selector, correction and vortex contraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_parent_presample_joint_reference
    (L rstar:ℕ) (βfreq ρ₀ α capEdit θhost ηcap ηProfile gapcap ζlimit:ℝ)
    (hr:4≤rstar) (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1)
    (hα:0<α) (hcap:0<capEdit) (hθhost:(1/2:ℝ)≤θhost) (hηcap:0<ηcap)
    (hmargin:α/2≤1/2 ∧ max (1/2) (cycleThreshold rstar)+(α/2)/2≤1)
    (hprofile:0<ηProfile) (hgapcap:0<gapcap) (hζlimit:0<ζlimit):
    let smin:=βfreq/200;let pstar:=ρ₀*smin/2;let ω:=ρ₀/4;
    let αcut:=min (α/8) (1/4:ℝ);
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∃Kdeep:ℕ,0<Kdeep ∧ ∃aDeep ε₀ ρdeep θdeep:ℝ,
      0<aDeep ∧ 0<ε₀ ∧ 0<ρdeep ∧ 0<θdeep ∧
      OrdinaryDeepRowsCutsEarlyBeforeLoad (rstar-1) Kdeep (α/2) ρ₀ pstar αcut c C aDeep ε₀ ρdeep θdeep ∧
    ∃δAbs h εabs εv:ℝ,
      OrdinaryWeightedCorrectionAfterEarly rstar (α/2) pstar ω δAbs h εabs εv ∧
      let εmax:=min aDeep (min (ρ₀/16) (1/8:ℝ));
      let capInner:=min εmax (min εabs εv);
      0<capInner ∧ capInner≤aDeep ∧ capInner≤ρ₀/16 ∧ capInner≤1/8 ∧
      capInner≤εabs ∧ capInner≤εv ∧
      ∃ηP:ℝ,0<ηP ∧ ηP≤ηcap ∧ ∃d:ℕ,∃hd:2≤d,
        OrdinaryOriginalPreSampleJointAtSpacing L rstar d βfreq ρ₀ α (α/2) capInner capEdit θhost
          (by omega) hβ hβ1 hρ hα ∧
        OrdinaryParentReferenceDeepJointAt (rstar-1) Kdeep d (by omega) hd (α/2) ρ₀ pstar ηP (by positivity)
          aDeep ρdeep θdeep ηProfile αcut ηcap gapcap ζlimit :=by
  intro smin pstar ω αcut
  obtain ⟨c,C,hc,hC,Kdeep,hK,aDeep,ε₀,ρdeep,θdeep,ha,hε,hρdeep,hθdeep,hdeep,
    δAbs,h,εabs,εv,hCorr,hInner,hA,hR,h8,hAbs,hV,ηP,hη,hηcap',d,hd,hPre,hparent⟩:=
    ordinary_deep_parent_presample_same_spacing L rstar βfreq ρ₀ α capEdit θhost ηcap
      hr hβ hβ1 hρ hρ1 hα hcap hθhost hηcap hmargin
  have hcut:0<αcut:=by dsimp [αcut]; positivity
  have hjoint:=ordinary_parent_reference_deep_joint_at (rstar-1) Kdeep d (by omega) hd (α/2) ρ₀ pstar ηP
    (by positivity) hρ aDeep ρdeep θdeep ηProfile αcut ha hρdeep hθdeep hprofile hcut
    ηcap gapcap ζlimit hηcap hgapcap hζlimit hparent
  exact ⟨c,C,hc,hC,Kdeep,hK,aDeep,ε₀,ρdeep,θdeep,ha,hε,hρdeep,hθdeep,hdeep,
    δAbs,h,εabs,εv,hCorr,hInner,hA,hR,h8,hAbs,hV,ηP,hη,hηcap',d,hd,hPre,hjoint⟩
end Oberwolfach
