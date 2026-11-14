module

public import Oberwolfach.OrdinaryOriginalThresholdPlacementMatchingRates
public import Oberwolfach.OrdinaryOriginalSelectorSpacingBounds
public import Oberwolfach.OrdinaryPlacementEarlyRateData

@[expose] public section
/-! Choose the original weighted selector and the independent reserved-list
placement hierarchy in one order, with one matching tolerance, spacing and
cutoff. The selector retains its original factor and sampling quantifiers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach

theorem ordinary_original_selector_placement_before_edit_cap
    (L rstar:ℕ) (βfreq ρ₀ α γList capInner θhost:ℝ)
    (hr:3 ≤ rstar) (hβfreq:0<βfreq) (hβ1:βfreq ≤ 1) (hρ₀:0<ρ₀) (hα:0<α)
    (hγList:0<γList) (hcapInner:0<capInner) (hθhost:1/2 ≤ θhost):
    let smin₀:=βfreq/200;let αCap:=5*ρ₀*smin₀^2/128;
    ∃m k:ℕ,∃βPlace lamPlace ζPlace ε:ℝ,∃dMin:ℕ,
      OrdinaryOriginalThresholdFamilyAt L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα m k ∧
      OrdinaryPlacementEarlyRateData γList ρ₀ smin₀ capInner βPlace lamPlace ζPlace ε dMin ∧
    ∀capEdit:ℝ,0<capEdit→
    ∃δ θ κ b z matchErr σ κ':ℝ,∃dNeed:ℕ,
      OrdinaryPlacementStage m dNeed αCap lamPlace ζPlace capEdit δ θ κ b z matchErr σ κ' ∧
    ∃βSel lamSel ζSel smin:ℝ,∃d K rank:ℕ,
      OrdinaryOriginalSelectorSpacingBounds rstar m dNeed dMin d K rank βfreq θ βSel lamSel ζSel smin ∧
    ∃ζret:ℝ,∃N:ℕ,∃lamMatch aRow γrow:ℝ,∃BO:Fin K → ℝ,
      OrdinaryPlacementAfterSpacing m d N αCap δ θ κ b z matchErr ζret ∧
      OrdinaryPlacementMatchingRateBounds K θ κ' b z δ matchErr lamMatch aRow γrow ∧
      (∀i,0<BO i) ∧
      ∃hd:2 ≤ d,OrdinaryOriginalThresholdAfterMatchingRates rstar m k d K hd βfreq ρ₀ α θ θhost
        lamMatch aRow γrow ζSel lamSel ζSel smin BO :=by
  intro smin₀ αCap
  have hsmin:0<smin₀:=by dsimp [smin₀];positivity
  obtain ⟨m,k,hAt⟩:=ordinary_original_threshold_family_at_exists L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα
  obtain ⟨βPlace,lamPlace,ζPlace,ε,hβ,hβPlace1,hlam,hζ,hbudget,hε,hεcap,hεlam,hεζ,hεfloor,hlocal,hgeometry,
    dMin,hdMin,hrates⟩:=ordinary_placement_hierarchy_before_matching γList ρ₀ smin₀ capInner hγList hρ₀ hsmin hcapInner
  have hEarly:OrdinaryPlacementEarlyRateData γList ρ₀ smin₀ capInner βPlace lamPlace ζPlace ε dMin:=
    ⟨hβ,hβPlace1,hlam,hζ,hbudget,hε,hεcap,hεlam,hεζ,hεfloor,hlocal,hgeometry,hdMin,hrates⟩
  refine ⟨m,k,βPlace,lamPlace,ζPlace,ε,dMin,hAt,hEarly,?_⟩
  intro capEdit hcapEdit
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hstage,βSel,lamSel,ζSel,smin,
    hβSel,hβSel1,hlamSel,hζSel,hsminSel,hsminEq,d,K,rank,hdMin',hdNeed,hd,hK,hrK,hrank,hrankm,hrankO,
    hdθ,hspace,hβK,hcut,hpost⟩:=
    ordinary_original_threshold_placement_spacing L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα m k hAt
      αCap lamPlace ζPlace capEdit hcapEdit hgeometry dMin
  have hSpacing:OrdinaryOriginalSelectorSpacingBounds rstar m dNeed dMin d K rank βfreq θ βSel lamSel ζSel smin:=
    ⟨hβSel,hβSel1,hlamSel,hζSel,hsminSel,hsminEq,hdMin',hdNeed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcut⟩
  obtain ⟨ζret,N,lamMatch,aRow,γrow,BO,hAfter,hmatches,hBO,hselect⟩:=
    ordinary_original_threshold_placement_matching_rates rstar m k d K rank dNeed hd hK hdNeed
      βfreq ρ₀ α θ βSel lamSel ζSel smin αCap lamPlace ζPlace capEdit δ κ b z matchErr σ κ'
      hζSel hspace hstage hpost θhost hθhost
  exact ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hstage,
    βSel,lamSel,ζSel,smin,d,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hmatches,hBO,hd,hselect⟩
end Oberwolfach
