module

public import Oberwolfach.OrdinaryDeepScaledRatesBeforeFailure
public import Oberwolfach.OrdinaryDeepSpacingErrorBeforeLateCap

@[expose] public section
/-! Choose one deep cap, target edit rate and correction rate before all
failure allowances and absorber sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_scaled_rates_late_vortex_error
    (rstar mWheel Kdeep d mMatch:ℕ) (hd:2≤d)
    (αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (hdeep:OrdinaryDeepRowsCutsEarlyBeforeFailure mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep)
    (aLoad ε capξ b Bweight ηHub Kdom eParent hParent εR εH:ℝ)
    (haLoad:0<aLoad) (haLoadA:aLoad≤a) (hε:0<ε) (hε1:ε<1/4) (hεa:ε≤a) (hερ:ε≤ρ₀/16)
    (hαdeep:0<αdeep) (hε₀:0<ε₀) (hcapξ:0<capξ) (hηHub:0<ηHub) (hK:2/ε≤Kdom) (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (hb:b≤c)
    (hB:(4*C/pmin^(3*mWheel+1))*Kdom^mWheel≤Bweight) (he:0<eParent) (hh:0<hParent) (hεR:0<εR) (hεH:0<εH)
    (lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace:ℝ)
    (hcolumns:OrdinaryEarlyUniformColumnsBeforeAbsorberShape d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace)
    (αcorr pstar ω δAbs hAbs εabs εv capExtra:ℝ) (hExtra:0<capExtra)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ω δAbs hAbs εabs εv):
    ∃ξdeep t eEvent hEvent cap ξedit ξAbs:ℝ,
      0<ξdeep ∧ ξdeep≤capξ ∧
      (∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤αdeep/8 ∧ β≤ε₀ ∧ β≤capξ ∧ β≤betaCap ∧ ξdeep+2*β<ηHub) ∧
      0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧ eEvent≤eParent ∧ hEvent≤hParent ∧
      0<ξedit ∧ ξedit≤cap*ε/1000 ∧ ξedit≤capExtra ∧ ξedit≤bList/8 ∧ ξedit≤bMatch ∧
      OrdinaryEarlyUniformColumnsAtRate d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace ξedit ∧
      0<ξAbs ∧ ξAbs≤cap*ε/1000 ∧ ξAbs≤capExtra ∧ ξAbs≤hAbs/100 ∧
      (∀mAbs:ℕ,∃aAbs bAbs:ℕ,OrdinaryWeightedCorrectionAfterAbsorberChoices rstar d hd mAbs aAbs bAbs αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs) ∧
      ∀χinner χdeep χone χtwo χcut:ℝ,0<χinner→0<χdeep→0<χone→0<χtwo→0<χcut→
        OrdinaryDeepRowsCutsAfterParameters mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
          aLoad ε ξdeep b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap :=by
  obtain ⟨ξdeep,hξ,hξcap,hβ⟩:=ordinary_deep_spacing_error_before_late_cap αdeep ε₀ capξ ηHub hαdeep hε₀ hcapξ hηHub
  obtain ⟨t,eEvent,hEvent,cap,ξedit,ξAbs,ht,hevent,hhevent,hcap,hebound,hhbound,
    hξedit,hξeditscale,hξeditextra,hξlist,hξmatch,hcolumns,hξAbs,hξAbsscale,hξAbsextra,hξAbsh,hcorr,hselect⟩:=
    ordinary_deep_scaled_rates_before_failure rstar mWheel Kdeep d mMatch hd αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep hdeep
      aLoad ε ξdeep b Bweight ηHub Kdom eParent hParent εR εH haLoad haLoadA hε hε1 hεa hερ hξ hK hKdom hb hB he hh hεR hεH
      lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace hcolumns αcorr pstar ω δAbs hAbs εabs εv capExtra hExtra hcorr
  exact ⟨ξdeep,t,eEvent,hEvent,cap,ξedit,ξAbs,hξ,hξcap,hβ,ht,hevent,hhevent,hcap,hebound,hhbound,
    hξedit,hξeditscale,hξeditextra,hξlist,hξmatch,hcolumns,hξAbs,hξAbsscale,hξAbsextra,hξAbsh,hcorr,hselect⟩
end Oberwolfach
