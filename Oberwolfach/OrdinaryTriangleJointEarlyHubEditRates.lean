module

public import Oberwolfach.OrdinaryOriginalPreSampleFixedJointRatesAt
public import Oberwolfach.OrdinaryTriangleCommonRatesFromOuterHubChoice

@[expose] public section
/-! Select the outer hub, matching and correction rates together.  The edit
rates in the original pre-sampling witness are the very same rates as those
chosen for the hub construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_joint_early_hub_edit_rates
    (L d m k dMin:ℕ) (hd:2≤d) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:OrdinaryOriginalPreSampleAtEarly L 3 d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      (by omega) hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly)
    (αhub pmin κhub c C:ℝ) (htri:OrdinaryTriangleHubEarlyBeforeFailure αhub ρ₀ pmin κhub c C)
    (aLoad ε:ℝ) (haLoad:0<aLoad) (haκ:aLoad≤κhub) (hε:0<ε) (hε1:ε<1/4) (hεκ:ε≤κhub) (hερ:ε≤ρ₀/16)
    (capξ ηHub Kdom ηbal ζlimit ηBudget:ℝ)
    (hαhub:0<αhub) (hκ:0<κhub) (hcapξ:0<capξ) (hηHub:0<ηHub) (hηbal:0<ηbal)
    (hζlimit:0<ζlimit) (hηBudget:0<ηBudget) (hc:0<c) (hC:0<C) (hpmin:0<pmin)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (buffer:ℕ) (hbuffer:2≤buffer)
    (αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly 3 αcorr pstar ω δAbs hAbs εabs εv):
    ∃bHub Bweight ξdeep t ζ δDeep δcap rate ξedit ξAbs:ℝ,
      0<bHub ∧ bHub≤c ∧ 0<Bweight ∧ (4*C/pmin^(3*2+1))*Kdom^2≤Bweight ∧
      0<ξdeep ∧ ξdeep≤capξ ∧
      (∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤αhub/8 ∧ β≤κhub ∧ β≤capξ ∧ β≤betaCap ∧ ξdeep+2*β<ηHub) ∧
      0<t ∧ 0<ζ ∧ ζ≤ζlimit ∧ 0<δDeep ∧ δDeep≤αhub ∧ 0<δcap ∧ δcap≤ζ/2 ∧ 0<rate ∧
      OrdinaryVortexBufferedTraceCapCostWitness ε ρ₀ αhub pmin pmin ηbal ζ δDeep δcap rate d buffer ∧
      OrdinaryTriangleHubAfterCapBeforeFailure d hd αhub ρ₀ pmin κhub aLoad ε ξdeep bHub Bweight ηHub δDeep δcap ∧
      OrdinaryOriginalPreSampleFixedJointRatesAt L 3 d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
        (by omega) hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly ε δcap ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs :=by
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd',hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns⟩:=hTail
  have hσ:0<σ:=by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hσ,_⟩:=hStage
    exact hσ
  let αCap:=5*ρ₀*(βfreq/200)^2/128
  let cBudget:=min (1/1024:ℝ) (min (αCap/4096) (1/2:ℝ)/8)
  let capExtra:=min σ (ηBudget/1000)
  have hExtra:0<capExtra:=by dsimp [capExtra];positivity
  obtain ⟨bHub,Bweight,ξdeep,t,ζ,δDeep,δcap,rate,ξedit,ξAbs,hb,hbc,hB,hBbound,hξ,hξcap,hβ,ht,hζ,hζlimit',hδ,hδα,hδcap,hδζ,hrate,htrace,
    hξedit,hξeditscale,hξeditextra,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbsscale,hξAbsextra,hξAbsh,hcorrAt,houter⟩:=
    ordinary_triangle_common_rates_from_outer_hub_choice d m hd αhub ρ₀ pmin κhub c C htri aLoad ε haLoad haκ hε hε1 hεκ hερ
      capξ ηHub Kdom ηbal ζlimit hαhub hκ hcapξ hηHub hηbal hζlimit hc hC hpmin hKdom buffer hbuffer
      lamPlace ζPlace b εearly cBudget θ z δ aRow γrow (θ/2) bMatch αCap hColumns
      αcorr pstar ω δAbs hAbs εabs εv capExtra hExtra hcorr
  have hξσ:ξedit≤σ:=hξeditextra.trans (min_le_left _ _)
  have hξη:ξedit≤ηBudget/1000:=hξeditextra.trans (min_le_right _ _)
  have hξAbsσ:ξAbs≤σ:=hξAbsextra.trans (min_le_left _ _)
  have hξAbsη:ξAbs≤ηBudget/1000:=hξAbsextra.trans (min_le_right _ _)
  refine ⟨bHub,Bweight,ξdeep,t,ζ,δDeep,δcap,rate,ξedit,ξAbs,hb,hbc,hB,hBbound,hξ,hξcap,hβ,ht,hζ,hζlimit',hδ,hδα,hδcap,hδζ,hrate,htrace,houter,?_⟩
  exact ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd',hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    hξedit,hξeditscale,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbsscale,hξAbsη,hξAbsσ,hξAbsh,hcorrAt⟩
end Oberwolfach
