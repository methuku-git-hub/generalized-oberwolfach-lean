module

public import Oberwolfach.OrdinaryTriangleInitialMarginsFixedToleranceBeforeSpacing
public import Oberwolfach.OrdinaryTriangleEarlyBalanceSelectors
public import Oberwolfach.OrdinaryTriangleJointEarlyHubEditRates

@[expose] public section
/-! Fix the sample tolerance, then choose the initial matching budget and
spacing, and finally select the hub and correction rates for that spacing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_matching_spacing_and_joint_rates
    (L m k dMin:ℕ) (βfreq ρ₀ αOriginal γList capInner θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L 3 d m k dMin βfreq ρ₀ αOriginal γList capInner capEdit θhost
        (by omega) hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly)
    (αhub pmin κhub c C cInitial:ℝ)
    (hInitial:OrdinaryTriangleInitialMatchingMarginSelector ρ₀ αhub pmin pmin cInitial)
    (htri:OrdinaryTriangleHubEarlyBeforeFailure αhub ρ₀ pmin κhub c C)
    (aLoad ε ηbal ζcert capOriginal:ℝ) (haLoad:0<aLoad) (haκ:aLoad≤κhub)
    (hε:0<ε) (hεsmall:ε<1/4) (hεκ:ε≤κhub) (hερ:ε≤ρ₀/16)
    (hηbal:0<ηbal) (hζcert:0<ζcert) (hOriginal:0<capOriginal)
    (capξ ηHub Kdom ζlimit:ℝ)
    (hαhub:0<αhub) (hκ:0<κhub) (hcapξ:0<capξ) (hηHub:0<ηHub) (hζlimit:0<ζlimit)
    (hc:0<c) (hC:0<C) (hpmin:0<pmin)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (buffer:ℕ) (hbuffer:2≤buffer)
    (αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly 3 αcorr pstar ω δAbs hAbs εabs εv):
    ∃δedit ηedit ηBudget capChosen:ℝ,0<δedit ∧ δedit≤αhub ∧ δedit≤ηbal ∧ 0<ηedit ∧
      0<ηBudget ∧ ηBudget≤ηedit ∧ 15*ηBudget≤ζcert*ε/2 ∧
      0<capChosen ∧ capChosen≤capOriginal ∧ capChosen≤ηBudget ∧
    ∃d:ℕ,∃hd:2≤d,
      (∀β:ℝ,0≤β→β≤1/4→β≤δedit→∃m₀ N:ℕ,1≤m₀ ∧
        OrdinaryInitialMatchingMarginsAt ρ₀ αhub pmin pmin ε ηbal cInitial δedit ηedit β d m₀ N) ∧
    ∃bHub Bweight ξdeep t ζ δDeep δcap rate ξedit ξAbs:ℝ,
      0<bHub ∧ bHub≤c ∧ 0<Bweight ∧ (4*C/pmin^(3*2+1))*Kdom^2≤Bweight ∧
      0<ξdeep ∧ ξdeep≤capξ ∧
      (∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤αhub/8 ∧ β≤κhub ∧ β≤capξ ∧ β≤betaCap ∧ ξdeep+2*β<ηHub) ∧
      0<t ∧ 0<ζ ∧ ζ≤ζlimit ∧ 0<δDeep ∧ δDeep≤αhub ∧ 0<δcap ∧ δcap≤ζ/2 ∧ 0<rate ∧
      OrdinaryVortexBufferedTraceCapCostWitness ε ρ₀ αhub pmin pmin ηbal ζ δDeep δcap rate d buffer ∧
      OrdinaryTriangleHubAfterCapBeforeFailure d hd αhub ρ₀ pmin κhub aLoad ε ξdeep bHub Bweight ηHub δDeep δcap ∧
      OrdinaryOriginalPreSampleFixedJointRatesAt L 3 d m k dMin βfreq ρ₀ αOriginal γList capInner capChosen θhost
        (by omega) hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly ε δcap ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs :=by
  obtain ⟨δedit,ηedit,ηBudget,capChosen,hδ,hδα,hδbal,hη,hBudget,hBudgetη,hsmall,hChosen,hcap,hcapBudget,d,hd,hpre,hmargins⟩:=
    ordinary_triangle_initial_margins_fixed_tolerance_before_spacing ρ₀ αhub pmin pmin cInitial hInitial ε ηbal ζcert capOriginal
      hε hεsmall hηbal hζcert hOriginal L 3 m k dMin βfreq αOriginal γList capInner θhost
      (by omega) hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly hTail
  obtain ⟨bHub,Bweight,ξdeep,t,ζ,δDeep,δcap,rate,ξedit,ξAbs,hb,hbc,hB,hBbound,hξ,hξcap,hβ,ht,hζ,hζlimit',hδDeep,hδαDeep,hδcap,hδζ,hrate,htrace,houter,hjoint⟩:=
    ordinary_triangle_joint_early_hub_edit_rates L d m k dMin hd βfreq ρ₀ αOriginal γList capInner capChosen θhost
      hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly hpre
      αhub pmin κhub c C htri aLoad ε haLoad haκ hε hεsmall hεκ hερ capξ ηHub Kdom ηbal ζlimit ηBudget
      hαhub hκ hcapξ hηHub hηbal hζlimit hBudget hc hC hpmin hKdom buffer hbuffer
      αcorr pstar ω δAbs hAbs εabs εv hcorr
  exact ⟨δedit,ηedit,ηBudget,capChosen,hδ,hδα,hδbal,hη,hBudget,hBudgetη,hsmall,hChosen,hcap,hcapBudget,d,hd,hmargins,
    bHub,Bweight,ξdeep,t,ζ,δDeep,δcap,rate,ξedit,ξAbs,hb,hbc,hB,hBbound,hξ,hξcap,hβ,ht,hζ,hζlimit',hδDeep,hδαDeep,hδcap,hδζ,hrate,htrace,houter,hjoint⟩
end Oberwolfach
