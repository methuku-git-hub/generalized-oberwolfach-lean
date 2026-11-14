module

public import Oberwolfach.OrdinaryDeepOriginalStaticFeasibleSelectedRows
public import Oberwolfach.OrdinaryDeepOriginalStaticParentSelectedRows
public import Oberwolfach.OrdinaryDeepOriginalStaticParentWithFixedMatching

@[expose] public section
/-! Shrink the original host margin before selecting the nontriangle parent,
wheel certificate and matching choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_original_static_selected_rows_original_cap
    (L rstar:ℕ) (βfreq ρ₀ α₀ θhost ηcap ηProfile gapcap ζlimit εmax capξ capWeight pcap:ℝ)
    (hr:4≤rstar) (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1)
    (hα₀:0<α₀) (hθhost:(1/2:ℝ)≤θhost) (hθ1:θhost<1)
    (hcycle:cycleThreshold rstar≤θhost) (hηcap:0<ηcap)
    (hprofile:0<ηProfile) (hgapcap:0<gapcap) (hζlimit:0<ζlimit)
    (hmax:0<εmax) (hcapξ:0<capξ) (hcapWeight:0<capWeight) (hpcap:0<pcap):
    ∃(α:ℝ) (hα:0<α),α≤α₀ ∧
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
        OrdinaryDeepParentAndEarlyEventStaticWithSelectedJointRowsAt (rstar-1) Kdeep (by omega) (α/2) ρ₀ βfreq ηP (by positivity)
          aDeep ρdeep θdeep ηProfile αcut ηcap gapcap ζlimit c C ε₀ εmax εearly capInner capξ capWeight pcap
          L rstar m k dMin (by omega) α (α/2) θhost hβ hβ1 hρ hα
          βPlace lamPlace ζPlace (α/2) pstar ω δAbs h εabs εv εmax :=by
  exact ordinary_deep_original_static_feasible_selected_rows L rstar βfreq ρ₀ α₀ θhost ηcap ηProfile gapcap ζlimit εmax capξ capWeight pcap εmax
    hr hβ hβ1 hρ hρ1 hα₀ hθhost hθ1 hcycle hηcap hprofile hgapcap hζlimit hmax hcapξ hcapWeight hpcap hmax
end Oberwolfach
