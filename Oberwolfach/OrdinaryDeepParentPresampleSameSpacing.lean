module

public import Oberwolfach.OrdinaryDeepParentPresampleMatchedLoad
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

theorem ordinary_deep_parent_presample_same_spacing
    (L rstar:ℕ) (βfreq ρ₀ α capEdit θhost ηcap:ℝ)
    (hr:4≤rstar) (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1)
    (hα:0<α) (hcap:0<capEdit) (hθhost:(1/2:ℝ)≤θhost) (hηcap:0<ηcap)
    (hmargin:α/2≤1/2 ∧ max (1/2) (cycleThreshold rstar)+(α/2)/2≤1):
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
        OrdinaryParentReferenceCompatibleChoices (rstar-1) Kdeep d (by omega) hd (α/2) ρ₀ pstar ηP (by positivity) :=by
  intro smin pstar ω αcut
  obtain ⟨c,C,hc,hC,Kdeep,hK,aDeep,ε₀,ρdeep,θdeep,ha,hε,hρdeep,hθdeep,hdeep,
    δAbs,h,εabs,εv,hCorr,hInner,hA,hR,h8,hAbs,hV,hPre,ηP,hη,hηcap',hparents⟩:=
    ordinary_deep_parent_presample_matched_load L rstar βfreq ρ₀ α capEdit θhost ηcap
      hr hβ hβ1 hρ hρ1 hα hcap hθhost hηcap hmargin
  obtain ⟨d,hd,hPre,hparent⟩:=ordinary_presample_parent_same_spacing L rstar Kdeep βfreq ρ₀ α (α/2)
    (min (min aDeep (min (ρ₀/16) (1/8:ℝ))) (min εabs εv)) capEdit θhost
    hr hβ hβ1 hρ hα hPre (α/2) pstar ηP (by positivity) hparents
  exact ⟨c,C,hc,hC,Kdeep,hK,aDeep,ε₀,ρdeep,θdeep,ha,hε,hρdeep,hθdeep,hdeep,
    δAbs,h,εabs,εv,hCorr,hInner,hA,hR,h8,hAbs,hV,ηP,hη,hηcap',d,hd,hPre,hparent⟩
end Oberwolfach
