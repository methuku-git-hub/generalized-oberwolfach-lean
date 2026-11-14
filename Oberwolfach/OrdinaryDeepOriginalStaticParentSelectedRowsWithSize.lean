module

public import Oberwolfach.OrdinaryDeepStaticParentSelectedRowsWithSize
public import Oberwolfach.OrdinaryDeepStaticParentWithSelectedJointRows
public import Oberwolfach.OrdinaryDeepOriginalParentAndEarlyEventStatic
public import Oberwolfach.OrdinaryDeepStaticParentWithFixedMatching

@[expose] public section
/-! The original feasible nontriangle hierarchy selects the parent and deep
wheel certificate before choosing matching cap, spacing, rates, and failures. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_original_static_parent_selected_rows_with_size
    (L rstar:ℕ) (βfreq ρ₀ α θhost ηcap ηProfile gapcap ζlimit εmax capξ capWeight pcap capOriginal:ℝ)
    (hr:4≤rstar) (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1)
    (hα:0<α) (hθhost:(1/2:ℝ)≤θhost) (hηcap:0<ηcap)
    (hmargin:α/2≤1/2 ∧ max (1/2) (cycleThreshold rstar)+(α/2)/2≤1)
    (hprofile:0<ηProfile) (hgapcap:0<gapcap) (hζlimit:0<ζlimit)
    (hmax:0<εmax) (hcapξ:0<capξ) (hcapWeight:0<capWeight) (hpcap:0<pcap) (hcapOriginal:0<capOriginal):
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
        OrdinaryDeepStaticParentSelectedRowsWithSizeAt (rstar-1) Kdeep (by omega) (α/2) ρ₀ βfreq ηP (by positivity)
          aDeep ρdeep θdeep ηProfile αcut ηcap gapcap ζlimit c C ε₀ εmax εearly capInner capξ capWeight pcap
          L rstar m k dMin (by omega) α (α/2) θhost hβ hβ1 hρ hα
          βPlace lamPlace ζPlace (α/2) pstar ω δAbs h εabs εv capOriginal :=by
  intro smin pstar ω αcut
  obtain ⟨c,C,hc,hC,Kdeep,hK,aDeep,ε₀,ρdeep,θdeep,ha,hε,hρdeep,hθdeep,hdeep,
    δAbs,h,εabs,εv,hCorr,hInner,hA,hR,h8,hAbs,hV,
    m,k,βPlace,lamPlace,ζPlace,εearly,dMin,hAt,hEarly,hTail,ηP,hη,hηcap',hparent⟩:=
    ordinary_deep_original_parent_and_early_event_static L rstar βfreq ρ₀ α θhost ηcap ηProfile gapcap ζlimit εmax capξ capWeight pcap
      hr hβ hβ1 hρ hρ1 hα hθhost hηcap hmargin hprofile hgapcap hζlimit hmax hcapξ hcapWeight hpcap
  have hm:7≤m:=hAt.2.1
  have hparentMatch:=ordinary_deep_static_parent_selected_rows_with_size (rstar-1) Kdeep (by omega) (α/2) ρ₀ βfreq ηP (by positivity)
    aDeep ρdeep θdeep ηProfile αcut ηcap gapcap ζlimit c C ε₀ εmax εearly
    (min (min aDeep (min (ρ₀/16) (1/8:ℝ))) (min εabs εv)) capξ capWeight pcap
    L rstar m k dMin (by omega) α (α/2) θhost hβ hβ1 hρ hα
    βPlace lamPlace ζPlace (α/2) pstar ω δAbs h εabs εv capOriginal
    hparent hTail hρ1 hθhost hCorr hm hAbs hV hcapOriginal hEarly
  exact ⟨c,C,hc,hC,Kdeep,hK,aDeep,ε₀,ρdeep,θdeep,ha,hε,hρdeep,hθdeep,hdeep,
    δAbs,h,εabs,εv,hCorr,hInner,hA,hR,h8,hAbs,hV,
    m,k,βPlace,lamPlace,ζPlace,εearly,dMin,hAt,hEarly,hTail,ηP,hη,hηcap',hparentMatch⟩
end Oberwolfach
