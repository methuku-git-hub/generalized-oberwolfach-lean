module

public import Oberwolfach.OrdinaryOriginalThresholdChooseMatchingRates
public import Oberwolfach.OrdinaryPlacementStage

@[expose] public section
/-! The placement tolerance and matching selector use the same chosen
matching tolerance and spacing, after the independent list rate is fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach

theorem ordinary_original_threshold_placement_spacing
    (L rstar:ℕ) (βfreq ρ₀ α:ℝ) (hr:3 ≤ rstar) (hβfreq:0<βfreq) (hβ1:βfreq ≤ 1)
    (hρ₀:0<ρ₀) (hα:0<α) (m k:ℕ)
    (hAt:OrdinaryOriginalThresholdFamilyAt L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα m k)
    (αCap lamList ζList capEdit:ℝ) (hcapEdit:0<capEdit)
    (hgeometry:OrdinaryLaterPlacementGeometry αCap lamList ζList) (dMin:ℕ):
    ∃δ θ κ b z matchErr σ κ':ℝ,∃dNeed:ℕ,
      OrdinaryPlacementStage m dNeed αCap lamList ζList capEdit δ θ κ b z matchErr σ κ' ∧
    ∃βSel lamSel ζSel smin:ℝ,0<βSel ∧ βSel ≤ 1 ∧ 0<lamSel ∧ 0<ζSel ∧ 0<smin ∧ smin=βfreq/200 ∧
    ∃d K rank:ℕ,dMin ≤ d ∧ dNeed ≤ d ∧ 2 ≤ d ∧ 3 ≤ K ∧ rstar ≤ K ∧ 2 ≤ rank ∧ 2*(m+1) ≤ rank ∧
      (∀i:Fin K,2*(longPaddedSeedExponent i+2) ≤ rank) ∧
      1/θ ≤ (d:ℝ) ∧ 1/(4*(d:ℝ)) ≤ 5*θ^2/256 ∧ 1/(2*(K:ℝ)) ≤ βfreq ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ) ≤ θ/2 ∧
      OrdinaryOriginalThresholdAfterSpacing rstar m k d K rank βfreq ρ₀ α θ βSel lamSel ζSel smin :=by
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hstage⟩:=hgeometry m capEdit hcapEdit
  have hstage':OrdinaryPlacementStage m dNeed αCap lamList ζList capEdit δ θ κ b z matchErr σ κ':=hstage
  obtain ⟨hδ,hδ1,hδlam,hδcap,hθ,hθ1,hθδ,hκ,hb,hz,herr,hσ,hσcap,hbFloor,hzFloor,
    hbζ,hbα,hbδ,hzb,hκ',hκ'κ,hdNeed,hbudget,hafter⟩:=hstage
  obtain ⟨βSel,lamSel,ζSel,smin,hβSel,hβSel1,hlamSel,hζSel,hsmin,hsminEq,
    d,K,rank,hBoth,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcut,hpost⟩:=
    ordinary_original_threshold_choose_spacing L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα m k hAt θ hθ hθ1 (max dNeed dMin)
  refine ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hstage',βSel,lamSel,ζSel,smin,
    hβSel,hβSel1,hlamSel,hζSel,hsmin,hsminEq,d,K,rank,?_,?_,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcut,hpost⟩
  · exact (le_max_right _ _).trans hBoth
  · exact (le_max_left _ _).trans hBoth
end Oberwolfach
