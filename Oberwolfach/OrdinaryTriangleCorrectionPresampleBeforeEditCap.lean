module

public import Oberwolfach.OrdinaryOriginalPreSampleBeforeEditCap
public import Oberwolfach.OrdinaryWeightedCorrectionAfterEarly
public import Oberwolfach.OrdinaryAssignedCorrectionOriginalRateChoice

@[expose] public section
/-! Select correction geometry and the early matching hierarchy while
postponing the edit cap; the returned vortex cap meets both choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_correction_presample_before_edit_cap
    (L:ℕ) (βfreq ρ₀ α εcap θhost:ℝ)
    (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1) (hα:0<α) (hεcap:0<εcap) (hθhost:1/2≤θhost):
    let smin:=βfreq/200;let pstar:=ρ₀*smin/2;let ω:=ρ₀/4;
    ∃δAbs hAbs εabs εv capInner:ℝ,
      OrdinaryWeightedCorrectionAfterEarly 3 (α/2) pstar ω δAbs hAbs εabs εv ∧
      0<capInner ∧ capInner≤εcap ∧ capInner≤εabs ∧ capInner≤εv ∧
    ∃m k:ℕ,∃βPlace lamPlace ζPlace εearly:ℝ,∃dMin:ℕ,
      0<εearly ∧ εearly≤capInner ∧
      OrdinaryOriginalThresholdFamilyAt L 3 βfreq ρ₀ α (by omega) hβ hβ1 hρ hα m k ∧
      OrdinaryPlacementEarlyRateData (α/2) ρ₀ smin capInner βPlace lamPlace ζPlace εearly dMin ∧
    ∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L 3 d m k dMin βfreq ρ₀ α (α/2) capInner capEdit θhost
        (by omega) hβ hβ1 hρ hα βPlace lamPlace ζPlace εearly :=by
  intro smin pstar ω
  obtain ⟨_hsmin,hpstar,hpstar1,hω,_⟩:=ordinary_assigned_correction_original_rate_choice βfreq ρ₀ hβ hβ1 hρ hρ1
  obtain ⟨δAbs,hAbs,εabs,εv,hδ,hδsmall,hh,hεabs,hεv,hcorrection⟩:=
    ordinary_weighted_selector_correction_unconditional_prior 3 (by omega) (α/2) pstar ω (by positivity) hpstar hpstar1 hω
  have hCorr:OrdinaryWeightedCorrectionAfterEarly 3 (α/2) pstar ω δAbs hAbs εabs εv:=
    ⟨hδ,hδsmall,hh,hεabs,hεv,hcorrection⟩
  let capInner:ℝ:=min εcap (min εabs εv)
  have hInner:0<capInner:=by dsimp [capInner];positivity
  have hMax:capInner≤εcap:=min_le_left _ _
  have hAbsCap:capInner≤εabs:=(min_le_right _ _).trans (min_le_left _ _)
  have hV:capInner≤εv:=(min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨m,k,βPlace,lamPlace,ζPlace,εearly,dMin,hAt,hEarly,hTail⟩:=
    ordinary_original_presample_before_edit_cap L 3 βfreq ρ₀ α (α/2) capInner θhost
      (by omega) hβ hβ1 hρ hα (by positivity) hInner hθhost
  have hearly:0<εearly ∧ εearly≤capInner:=by
    obtain ⟨_,_,_,_,_,he,hecap,_⟩:=hEarly
    exact ⟨he,hecap⟩
  exact ⟨δAbs,hAbs,εabs,εv,capInner,hCorr,hInner,hMax,hAbsCap,hV,m,k,βPlace,lamPlace,ζPlace,εearly,dMin,
    hearly.1,hearly.2,hAt,hEarly,hTail⟩
end Oberwolfach
