module

public import Oberwolfach.OrdinaryOriginalPreSampleWithEditRatesAt

@[expose] public section
/-! Select the matching and correction edit rates after the certificate
and the placement, while preserving their common event cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach

theorem ordinary_presample_choose_edit_rates
    (L rstar d m k dMin:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly)
    (εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (hε:0<εvortex) (hcap:0<capHub) (hη:0<ηBudget)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ω δAbs hAbs εabs εv):
    OrdinaryOriginalPreSampleWithEditRatesAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv :=by
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns⟩:=hTail
  have hσ:0<σ:=by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hσ,_⟩:=hStage
    exact hσ
  let αCap:=5*ρ₀*(βfreq/200)^2/128
  let cBudget:=min (1/1024:ℝ) (min (αCap/4096) (1/2:ℝ)/8)
  obtain ⟨ξedit,ξAbs,hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,
    hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt⟩:=
    ordinary_deep_edit_rates_after_certificate rstar d m hd εvortex capHub ηBudget σ hε hcap hη hσ
      lamPlace ζPlace b εearly cBudget θ z δ aRow γrow (θ/2) bMatch αCap hColumns
      αcorr pstar ω δAbs hAbs εabs εv hcorr
  exact ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    ξedit,ξAbs,hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt⟩
end Oberwolfach
