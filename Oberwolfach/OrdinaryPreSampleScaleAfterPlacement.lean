module

public import Oberwolfach.OrdinarySelectedUniformTrackedPlacement
public import Oberwolfach.OrdinaryOriginalPreSampleScaledEditRatesAt

@[expose] public section
/-! Choose the vortex contraction after the placement tolerance, while still
choosing edit rates before absorber sizes, the graph and the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach

theorem ordinary_presample_scale_after_placement
    (L rstar d m k dMin:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace εearly:ℝ) (hearly:0<εearly)
    (hAt:OrdinaryOriginalThresholdFamilyAt L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα m k)
    (hEarly:OrdinaryPlacementEarlyRateData γList ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace εearly dMin)
    (hTail:OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly)
    (εlimit capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (hlimit:0<εlimit) (hcap:0<capHub) (hη:0<ηBudget)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ω δAbs hAbs εabs εv):
    ∃εvortex:ℝ,0<εvortex ∧ εvortex≤εlimit ∧
      OrdinaryOriginalPreSampleScaledEditRatesAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv :=by
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns⟩:=hTail
  have hδ:0<δ:=hStage.1
  have hσ:0<σ:=by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hσ,_⟩:=hStage
    exact hσ
  let αCap:=5*ρ₀*(βfreq/200)^2/128
  have hαCap:0<αCap:=by dsimp [αCap];positivity
  let cBudget:=min (1/1024:ℝ) (min (αCap/4096) (1/2:ℝ)/8)
  let εvortex:=min (δ/2) (min αCap (min εearly εlimit))
  have hε:0<εvortex:=by dsimp [εvortex];positivity
  have hδcap:εvortex≤δ/2:=min_le_left _ _
  have hαcap:εvortex≤αCap:=(min_le_right _ _).trans (min_le_left _ _)
  have hearlycap:εvortex≤εearly:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlimitcap:εvortex≤εlimit:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨ξedit,ξAbs,hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,
    hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt⟩:=
    ordinary_deep_edit_rates_after_certificate rstar d m hd εvortex capHub ηBudget σ hε hcap hη hσ
      lamPlace ζPlace b εearly cBudget θ z δ aRow γrow (θ/2) bMatch αCap hColumns
      αcorr pstar ω δAbs hAbs εabs εv hcorr
  have hbMatch:0<bMatch:=hξedit.trans_le hξmatch
  have htracked:=ordinary_selected_uniform_tracked_placement L rstar m k dNeed dMin d K rank βfreq ρ₀ α
    hr hβfreq hβ1 hρ₀ hα hAt γList (βfreq/200) capInner βPlace lamPlace ζPlace εearly hEarly
    capEdit δ θ κ b z matchErr σ κ' hStage βSel lamSel ζSel smin hSpacing
    lamMatch aRow γrow hMatching bMatch ξedit ζret hbMatch hξedit
  refine ⟨εvortex,hε,hlimitcap,?_⟩
  exact ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,hε,hδcap,hαcap,hearlycap,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    ξedit,ξAbs,hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,htracked,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt⟩
end Oberwolfach
