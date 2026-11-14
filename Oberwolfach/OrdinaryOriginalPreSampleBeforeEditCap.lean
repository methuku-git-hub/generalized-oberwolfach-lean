module

public import Oberwolfach.OrdinaryOriginalSelectorPlacementBeforeEditCap
public import Oberwolfach.OrdinaryOriginalPreSampleAtEarly
public import Oberwolfach.OrdinaryOriginalThresholdChooseMatchCore
public import Oberwolfach.OrdinarySelectedUniformEditBeforeAbsorber

@[expose] public section
/-! Preserve the early vortex and list scales while postponing the actual
matching and placement edit cap until after the wheel certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach

theorem ordinary_original_presample_before_edit_cap
    (L rstar:ℕ) (βfreq ρ₀ α γList capInner θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (hγList:0<γList) (hcapInner:0<capInner) (hθhost:1/2≤θhost):
    let smin₀:=βfreq/200;
    ∃m k:ℕ,∃βPlace lamPlace ζPlace ε:ℝ,∃dMin:ℕ,
      OrdinaryOriginalThresholdFamilyAt L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα m k ∧
      OrdinaryPlacementEarlyRateData γList ρ₀ smin₀ capInner βPlace lamPlace ζPlace ε dMin ∧
    ∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace ε :=by
  intro smin₀
  obtain ⟨m,k,βPlace,lamPlace,ζPlace,ε,dMin,hAt,hEarly,hTail⟩:=
    ordinary_original_selector_placement_before_edit_cap L rstar βfreq ρ₀ α γList capInner θhost
      hr hβfreq hβ1 hρ₀ hα hγList hcapInner hθhost
  refine ⟨m,k,βPlace,lamPlace,ζPlace,ε,dMin,hAt,hEarly,?_⟩
  intro capEdit hcap
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,
    βSel,lamSel,ζSel,smin,d,K,rank,hSpacing,ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect⟩:=hTail capEdit hcap
  obtain ⟨τ,tMatch,ξMatch,bMatch,hChoice⟩:=ordinary_original_threshold_choose_match_core
    rstar m k d K hd βfreq ρ₀ α θ θhost lamMatch aRow γrow ζSel lamSel ζSel smin BO hSelect
  have hbMatch:0<bMatch:=hChoice.2.2.2.1
  have hEdit:=ordinary_selected_uniform_edit_before_absorber L rstar m k dNeed dMin d K rank
    βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα hAt γList (βfreq/200) capInner βPlace lamPlace ζPlace ε hEarly
    capEdit δ θ κ b z matchErr σ κ' hStage βSel lamSel ζSel smin hSpacing lamMatch aRow γrow hMatching bMatch hbMatch
  exact ⟨d,hd,δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hEdit⟩
end Oberwolfach
