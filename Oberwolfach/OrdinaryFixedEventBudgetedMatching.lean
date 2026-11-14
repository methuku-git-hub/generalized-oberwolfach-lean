module

public import Oberwolfach.OrdinaryPreSampleForInitialPlacementBudget
public import Oberwolfach.OrdinaryFixedEventJointMatchingRates
public import Oberwolfach.OrdinaryGeneralFixedRatesToJointThresholds

@[expose] public section
/-! Once the wheel certificate gives its initial tolerance, choose its
placement budget, matching spacing and rates before failure allowances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem ordinary_fixed_event_budgeted_matching
    (L rstar m k dMin:ℕ) (hr:3≤rstar)
    (βfreq ρ₀ α γList capInner θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hρ1:ρ₀≤1) (hα:0<α) (hθhost:1/2≤θhost)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly)
    (ε cap ηedit ζcert capOriginal αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (hε:0<ε) (hcap:0<cap) (hηedit:0<ηedit) (hζcert:0<ζcert) (hOriginal:0<capOriginal)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ω δAbs hAbs εabs εv)
    (hm:7≤m) (hεearly:ε≤εearly) (habs:ε≤εabs) (hv:ε≤εv)
    (hEarly:OrdinaryPlacementEarlyRateData (α/2) ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace εearly dMin):
    ∃ηBudget capEdit:ℝ,0<ηBudget ∧ ηBudget≤ηedit ∧ 15*ηBudget≤ζcert*ε/2 ∧
      0<capEdit ∧ capEdit≤capOriginal ∧ capEdit≤ηBudget ∧
    ∃d:ℕ,∃hd:2≤d,∃ξedit ξAbs:ℝ, ξedit≤cap ∧ ξAbs≤cap ∧
      OrdinaryOriginalPreSampleFixedJointRatesAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs ∧
      ∀(βv:ℝ) (mv:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ),
        0<ζ→0<χpair→0<χlist→0<χbal→0<χbd→0<χnbr→0<χpairR→0<χpath→
        0<χlocal→0<χglobal→0<χhub→0<χcol→
        OrdinaryOriginalPreSampleJointThresholdsSeparateListsAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
          hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv
          mv (2*mv) 10 ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol ξedit ξAbs βv :=by
  obtain ⟨ηBudget,capEdit,hBudget,hBudgetη,hsmall,hEdit,hEditOriginal,hEditBudget,d,hd,hTailAt⟩:=
    ordinary_presample_for_initial_placement_budget L rstar m k dMin βfreq ρ₀ α γList capInner θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly hTail capOriginal ηedit ζcert ε hOriginal hηedit hζcert hε
  obtain ⟨ξedit,ξAbs,hξcap,hξAbscap,hjoint⟩:=
    ordinary_fixed_event_joint_matching_rates L rstar d m k dMin hr hd βfreq ρ₀ α γList capInner capEdit θhost
      hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly hTailAt ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv hε hcap hBudget hcorr
  refine ⟨ηBudget,capEdit,hBudget,hBudgetη,hsmall,hEdit,hEditOriginal,hEditBudget,d,hd,ξedit,ξAbs,hξcap,hξAbscap,hjoint,?_⟩
  exact ordinary_general_fixed_rates_to_joint_thresholds L rstar d m k dMin hr βfreq ρ₀ α γList capInner capEdit θhost
    hβfreq hβ1 hρ₀ hρ1 hα hθhost βPlace lamPlace ζPlace εearly ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs
    hjoint hm hε hεearly habs hv hEarly
end Oberwolfach
