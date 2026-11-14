module

public import Oberwolfach.OrdinaryOriginalThresholdPlacementSpacing
public import Oberwolfach.OrdinaryPlacementAfterSpacing

@[expose] public section
/-! Select the matching rates at the same cutoff and spacing chosen by the
placement hierarchy, and retain the full original weighted selector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach

theorem ordinary_original_threshold_placement_matching_rates
    (rstar m k d K rank dNeed:ℕ) (hd:2 ≤ d) (hK:3 ≤ K) (hdNeed:dNeed ≤ d)
    (βfreq ρ₀ α θ βSel lamSel ζSel smin αCap lamList ζList capEdit δ κ b z matchErr σ κ':ℝ)
    (hζSel:0<ζSel) (hspace:1/(4*(d:ℝ)) ≤ 5*θ^2/256)
    (hstage:OrdinaryPlacementStage m dNeed αCap lamList ζList capEdit δ θ κ b z matchErr σ κ')
    (hpost:OrdinaryOriginalThresholdAfterSpacing rstar m k d K rank βfreq ρ₀ α θ βSel lamSel ζSel smin)
    (θhost:ℝ) (hθhost:1/2 ≤ θhost):
    ∃ζret:ℝ,∃N:ℕ,∃lam aRow γ:ℝ,∃BO:Fin K → ℝ,
      OrdinaryPlacementAfterSpacing m d N αCap δ θ κ b z matchErr ζret ∧
      OrdinaryPlacementMatchingRateBounds K θ κ' b z δ matchErr lam aRow γ ∧
      (∀i,0<BO i) ∧
      OrdinaryOriginalThresholdAfterMatchingRates rstar m k d K hd βfreq ρ₀ α θ θhost
        lam aRow γ ζSel lamSel ζSel smin BO :=by
  obtain ⟨hδ,hδ1,hδlam,hδcap,hθ,hθ1,hθδ,hκ,hb,hz,herr,hσ,hσcap,hbFloor,hzFloor,
    hbζ,hbα,hbδ,hzb,hκ',hκ'κ,hdNeed',hbudget,hafter⟩:=hstage
  obtain ⟨ζret,hζret,hcapacity,hsize,hret,N,hN,hpow,hmatching⟩:=hafter d hdNeed hspace
  obtain ⟨lam,aRow,γ,hrates⟩:=hmatching K (by omega)
  have hrates':OrdinaryPlacementMatchingRateBounds K θ κ' b z δ matchErr lam aRow γ:=hrates
  obtain ⟨hlam,hlam1,ha,hγ,hlamθ,hγlam,haκ,hγκ,hab,haz,hγz,hγθ,haBound,
    hslack0,hslack8,hslackErr,hslack,hrows⟩:=hrates
  obtain ⟨BO,hBO,hselect⟩:=ordinary_original_threshold_choose_matching_rates
    rstar m k d K rank hd βfreq ρ₀ α θ βSel lamSel ζSel smin hpost θhost hθhost
    lam aRow γ ζSel hlam hlam1 ha hγ hζSel haBound hslack
  exact ⟨ζret,N,lam,aRow,γ,BO,⟨hζret,hcapacity,hsize,hret,hN,hpow⟩,hrates',hBO,hselect⟩
end Oberwolfach
