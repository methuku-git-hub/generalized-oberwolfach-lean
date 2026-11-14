module

public import Oberwolfach.OrdinaryDeepParentJointBeforeSpacing
public import Oberwolfach.OrdinaryDeepParentChooseEarlyEventStatic
public import Oberwolfach.OrdinaryOriginalParentDeepQuarter
public import Oberwolfach.OrdinaryParentReferenceDeepJointBeforeSpacingAt
public import Oberwolfach.OrdinaryOriginalParentReferenceBeforeSpacing
public import Oberwolfach.OrdinaryOriginalPreSampleBeforeEditCap
public import Oberwolfach.OrdinaryOriginalJointCorrectionPlacementChoices

@[expose] public section
/-! For reserved cycles of length at least four, select the deep wheel
constants before the ordinary selector, correction and vortex contraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_original_parent_and_early_event_static
    (L rstar:ℕ) (βfreq ρ₀ α θhost ηcap ηProfile gapcap ζlimit εmax capξ capWeight pcap:ℝ)
    (hr:4≤rstar) (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1)
    (hα:0<α) (hθhost:(1/2:ℝ)≤θhost) (hηcap:0<ηcap)
    (hmargin:α/2≤1/2 ∧ max (1/2) (cycleThreshold rstar)+(α/2)/2≤1)
    (hprofile:0<ηProfile) (hgapcap:0<gapcap) (hζlimit:0<ζlimit)
    (hmax:0<εmax) (hcapξ:0<capξ) (hcapWeight:0<capWeight) (hpcap:0<pcap):
    let smin:=βfreq/200;let pstar:=ρ₀*smin/2;let ω:=ρ₀/4;
    let αcut:=min (α/8) (1/4:ℝ);
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∃Kdeep:ℕ,0<Kdeep ∧ ∃aDeep ε₀ ρdeep θdeep:ℝ,
      0<aDeep ∧ 0<ε₀ ∧ 0<ρdeep ∧ 0<θdeep ∧
      OrdinaryDeepRowsCutsEarlyBeforeLoad (rstar-1) Kdeep (α/2) ρ₀ pstar αcut c C aDeep ε₀ ρdeep θdeep ∧
    ∃δAbs h εabs εv:ℝ,
      OrdinaryWeightedCorrectionAfterEarly rstar (α/2) pstar ω δAbs h εabs εv ∧
      let εmaxInner:=min aDeep (min (ρ₀/16) (1/8:ℝ));
      let capInner:=min εmaxInner (min εabs εv);
      0<capInner ∧ capInner≤aDeep ∧ capInner≤ρ₀/16 ∧ capInner≤1/8 ∧
      capInner≤εabs ∧ capInner≤εv ∧
      ∃m k:ℕ,∃βPlace lamPlace ζPlace εearly:ℝ,∃dMin:ℕ,
        OrdinaryOriginalThresholdFamilyAt L rstar βfreq ρ₀ α (by omega) hβ hβ1 hρ hα m k ∧
        OrdinaryPlacementEarlyRateData (α/2) ρ₀ smin capInner βPlace lamPlace ζPlace εearly dMin ∧
      (∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
        OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α (α/2) capInner capEdit θhost
          (by omega) hβ hβ1 hρ hα βPlace lamPlace ζPlace εearly) ∧
      ∃ηP:ℝ,0<ηP ∧ ηP≤ηcap ∧
        OrdinaryDeepParentAndEarlyEventStaticAt (rstar-1) Kdeep (by omega) (α/2) ρ₀ βfreq ηP (by positivity)
          aDeep ρdeep θdeep ηProfile αcut ηcap gapcap ζlimit c C ε₀ εmax εearly capInner capξ capWeight pcap :=by
  intro smin pstar ω αcut
  obtain ⟨c,C,hc,hC,Kdeep,hK,aDeep,ε₀,ρdeep,θdeep,ha,hε,hρdeep,hθdeep,hdeep,
    δAbs,h,εabs,εv,hCorr,hInner,hA,hR,h8,hAbs,hV,
    m,k,βPlace,lamPlace,ζPlace,εearly,dMin,hAt,hEarly,hTail,ηP,hη,hηcap',hparent⟩:=
    ordinary_deep_parent_joint_before_spacing L rstar βfreq ρ₀ α θhost ηcap ηProfile gapcap ζlimit
      hr hβ hβ1 hρ hρ1 hα hθhost hηcap hmargin hprofile hgapcap hζlimit
  have hearly:0<εearly:=hEarly.2.2.2.2.2.1
  have hparentStatic:=ordinary_original_parent_deep_quarter rstar Kdeep hr βfreq ρ₀ α ηP hβ hβ1 hρ hρ1 hα hη hmargin
    aDeep ρdeep θdeep ηProfile αcut ha hρdeep hθdeep hprofile (by dsimp [αcut];positivity)
    ηcap gapcap ζlimit hηcap hgapcap hζlimit
  have hEvent:=ordinary_deep_parent_choose_early_event_static (rstar-1) Kdeep (by omega) (α/2) ρ₀ βfreq ηP
    (by positivity) hρ hρ1 hβ hβ1 aDeep ρdeep θdeep ηProfile αcut ηcap gapcap ζlimit
    c C ε₀ εmax εearly (min (min aDeep (min (ρ₀/16) (1/8:ℝ))) (min εabs εv)) capξ capWeight pcap
    ha hc hC hε hmax hearly hInner hcapξ hcapWeight hpcap hdeep hparentStatic
  exact ⟨c,C,hc,hC,Kdeep,hK,aDeep,ε₀,ρdeep,θdeep,ha,hε,hρdeep,hθdeep,hdeep,
    δAbs,h,εabs,εv,hCorr,hInner,hA,hR,h8,hAbs,hV,
    m,k,βPlace,lamPlace,ζPlace,εearly,dMin,hAt,hEarly,hTail,ηP,hη,hηcap',hEvent⟩
end Oberwolfach
