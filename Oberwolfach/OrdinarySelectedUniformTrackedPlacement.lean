module

public import Oberwolfach.OrdinaryEarlyUniformTrackedPlacementShape
public import Oberwolfach.OrdinaryOriginalSelectorSpacingBounds
public import Oberwolfach.OrdinaryPlacementEarlyRateData
public import Oberwolfach.OrdinaryPlacementMatchingRateBounds

@[expose] public section
/-! The actual early selector and placement inequalities discharge the
numerical inputs of the fixed-reservoir, uniform-edit theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach

theorem ordinary_selected_uniform_tracked_placement
    (L rstar m k dNeed dMin d K rank:ℕ)
    (βfreq ρ₀ α:ℝ) (hr:3 ≤ rstar) (hβfreq:0<βfreq) (hβ1:βfreq ≤ 1) (hρ₀:0<ρ₀) (hα:0<α)
    (hAt:OrdinaryOriginalThresholdFamilyAt L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα m k)
    (γList smin capInner βPlace lamPlace ζPlace ε:ℝ)
    (hEarly:OrdinaryPlacementEarlyRateData γList ρ₀ smin capInner βPlace lamPlace ζPlace ε dMin)
    (capEdit δ θ κ bRate z matchErr σ κ':ℝ)
    (hStage:OrdinaryPlacementStage m dNeed (5*ρ₀*smin^2/128) lamPlace ζPlace capEdit δ θ κ bRate z matchErr σ κ')
    (βSel lamSel ζSel sminSel:ℝ)
    (hSpacing:OrdinaryOriginalSelectorSpacingBounds rstar m dNeed dMin d K rank βfreq θ βSel lamSel ζSel sminSel)
    (lamMatch aRow γrow:ℝ)
    (hMatching:OrdinaryPlacementMatchingRateBounds K θ κ' bRate z δ matchErr lamMatch aRow γrow)
    (bMatch ξcap ζret:ℝ) (hbMatch:0<bMatch) (hξcap:0<ξcap):
    let αCap:=5*ρ₀*smin^2/128
    let cBudget:=min (1/1024:ℝ) (min (αCap/4096) (1/2:ℝ)/8);
    OrdinaryEarlyUniformTrackedPlacementShape d m
      lamPlace ζPlace bRate ε cBudget θ z aRow γrow (θ/2) bMatch αCap δ ζret κ ξcap :=by
  intro αCap cBudget
  obtain ⟨_,hm,_,_,_,_⟩:=hAt
  obtain ⟨hβPlace,hβPlace1,hlamPlace,hζPlace,hlistBudget,hε,hεcap,hεlam,hεζ,hεfloor,hlocal,hgeometry,hdMin,hrates⟩:=hEarly
  obtain ⟨hδ,hδ1,hδlam,hδcap,hθ,hθ1,hθδ,hκ,hb,hz,herr,hσ,hσcap,hbFloor,hzFloor,
    hbζ,hbα,hbδ,hzb,hκ',hκ'κ,hdNeed,hbudget,hafter⟩:=hStage
  obtain ⟨hβSel,hβSel1,hlamSel,hζSel,hsminSel,hsminEq,hdMin',hdNeed',hd,hK,hrK,hrank,hrankm,hrankO,
    hdθ,hspace,hβK,hcut⟩:=hSpacing
  obtain ⟨hlamMatch,hlamMatch1,haRow,hγrow,hlamθ,hγlam,haκ,hγκ,haRate,haz,hγz,hγθ,haBound,
    hslack0,hslack8,hslackErr,hslack,hrows⟩:=hMatching
  have hεlist:ε ≤ min (lamPlace/4) (ζPlace/8):=le_min hεlam hεζ
  have hζ0:0 ≤ θ/2:=by linarith
  have hζθ:θ/2 ≤ θ:=by linarith
  exact ordinary_early_uniform_tracked_placement d m
    lamPlace ζPlace bRate ε cBudget θ z aRow γrow (θ/2) bMatch αCap δ ζret κ ξcap
    hδ hξcap hlamPlace hζPlace hb hbMatch hm hd hdθ hθ hθ1 hz hεfloor hεlist hzFloor
    haz hγz haRate hγθ hζ0 hζθ hbFloor hlocal
end Oberwolfach
