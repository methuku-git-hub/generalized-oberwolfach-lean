module

public import Oberwolfach.OrdinaryFixedEventJointMatchingRates
public import Oberwolfach.OrdinaryGeneralFixedRatesToJointThresholds

@[expose] public section
/-! Retain the previously selected wheel-event cap while choosing matching
and correction rates before all failure budgets and terminal sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem ordinary_fixed_event_rates_and_thresholds
    (L rstar d m k dMin:ℕ) (hr:3≤rstar) (hd:2≤d)
    (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hρ1:ρ₀≤1) (hα:0<α) (hθhost:1/2≤θhost)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly)
    (ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (hε:0<ε) (hcap:0<cap) (hη:0<ηBudget)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ω δAbs hAbs εabs εv)
    (hm:7≤m) (hεearly:ε≤εearly) (habs:ε≤εabs) (hv:ε≤εv)
    (hEarly:OrdinaryPlacementEarlyRateData (α/2) ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace εearly dMin):
    ∃ξedit ξAbs:ℝ, ξedit≤cap ∧ ξAbs≤cap ∧
      ∀(βv:ℝ) (mv:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ),
        0<ζ→0<χpair→0<χlist→0<χbal→0<χbd→0<χnbr→0<χpairR→0<χpath→
        0<χlocal→0<χglobal→0<χhub→0<χcol→
        OrdinaryOriginalPreSampleJointThresholdsSeparateListsAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
          hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv
          mv (2*mv) 10 ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol ξedit ξAbs βv :=by
  obtain ⟨ξedit,ξAbs,hξcap,hξAbscap,hjoint⟩:=
    ordinary_fixed_event_joint_matching_rates L rstar d m k dMin hr hd βfreq ρ₀ α γList capInner capEdit θhost
      hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly hTail ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv hε hcap hη hcorr
  exact ⟨ξedit,ξAbs,hξcap,hξAbscap,
    ordinary_general_fixed_rates_to_joint_thresholds L rstar d m k dMin hr βfreq ρ₀ α γList capInner capEdit θhost
      hβfreq hβ1 hρ₀ hρ1 hα hθhost βPlace lamPlace ζPlace εearly ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs
      hjoint hm hε hεearly habs hv hEarly⟩
end Oberwolfach
