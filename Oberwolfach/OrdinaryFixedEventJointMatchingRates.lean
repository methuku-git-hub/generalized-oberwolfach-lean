module

public import Oberwolfach.OrdinaryOriginalPreSampleFixedJointRatesAt

@[expose] public section
/-! Choose the matching and correction rates under the cap of an already
selected wheel event. The cap and both rates remain fixed before failures. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem ordinary_fixed_event_joint_matching_rates
    (L rstar d m k dMin:ℕ) (hr:3≤rstar) (hd:2≤d)
    (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly)
    (ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (hε:0<ε) (hcap:0<cap) (hη:0<ηBudget)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ω δAbs hAbs εabs εv):
    ∃ξedit ξAbs:ℝ,
      ξedit≤cap ∧ ξAbs≤cap ∧ OrdinaryOriginalPreSampleFixedJointRatesAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs :=by
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd',hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns⟩:=hTail
  have hσ:0<σ:=by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hσ,_⟩:=hStage;exact hσ
  let αCap:=5*ρ₀*(βfreq/200)^2/128
  let cBudget:=min (1/1024:ℝ) (min (αCap/4096) (1/2:ℝ)/8)
  let capExtra:=min σ cap
  have hExtra:0<capExtra:=by dsimp [capExtra]; positivity
  obtain ⟨ξedit,ξAbs,hξedit,hξscale,hξη,hξextra,hξlist,hξmatch,hcolumnsAt,
    hξAbs,hξAbsscale,hξAbsη,hξAbsextra,hξAbsh,hcorrAt⟩:=
    ordinary_deep_edit_rates_after_certificate rstar d m hd ε cap ηBudget capExtra hε hcap hη hExtra
      lamPlace ζPlace b εearly cBudget θ z δ aRow γrow (θ/2) bMatch αCap hColumns
      αcorr pstar ω δAbs hAbs εabs εv hcorr
  have hξσ:ξedit≤σ:=hξextra.trans (min_le_left _ _)
  have hξcap:ξedit≤cap:=hξextra.trans (min_le_right _ _)
  have hξAbsσ:ξAbs≤σ:=hξAbsextra.trans (min_le_left _ _)
  have hξAbscap:ξAbs≤cap:=hξAbsextra.trans (min_le_right _ _)
  refine ⟨ξedit,ξAbs,hξcap,hξAbscap,?_⟩
  exact ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd',hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    hξedit,hξscale,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbsscale,hξAbsη,hξAbsσ,hξAbsh,hcorrAt⟩
end Oberwolfach
