module

public import Oberwolfach.OrdinaryDeepCapBeforeLoadChoice
public import Oberwolfach.OrdinaryEarlyUniformColumnsChooseSmaller
public import Oberwolfach.OrdinaryCorrectionRateBeforeAbsorberUnderCap

@[expose] public section
/-! Choose one deep cap, target edit rate and correction rate before all
failure allowances and absorber sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_scaled_rates_before_load
    (rstar mWheel Kdeep d mMatch:ℕ) (hd:2≤d)
    (αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (hdeep:OrdinaryDeepRowsCutsEarlyBeforeLoad mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep)
    (ε ξdeep b Bweight ηHub Kdom eParent hParent:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεa:ε≤a) (hερ:ε≤ρ₀/16)
    (hξ:0<ξdeep) (hK:2/ε≤Kdom) (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (hb:b≤c)
    (hB:(4*C/pmin^(3*mWheel+1))*Kdom^mWheel≤Bweight) (he:0<eParent) (hh:0<hParent)
    (lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace:ℝ)
    (hcolumns:OrdinaryEarlyUniformColumnsBeforeAbsorberShape d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace)
    (αcorr pstar ω δAbs hAbs εabs εv capExtra:ℝ) (hExtra:0<capExtra)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ω δAbs hAbs εabs εv):
    ∃t eEvent hEvent cap ξedit ξAbs:ℝ,
      0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧ eEvent≤eParent ∧ hEvent≤hParent ∧
      0<ξedit ∧ ξedit≤cap*ε/1000 ∧ ξedit≤capExtra ∧ ξedit≤bList/8 ∧ ξedit≤bMatch ∧
      OrdinaryEarlyUniformColumnsAtRate d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace ξedit ∧
      0<ξAbs ∧ ξAbs≤cap*ε/1000 ∧ ξAbs≤capExtra ∧ ξAbs≤hAbs/100 ∧
      (∀mAbs:ℕ,∃aAbs bAbs:ℕ,OrdinaryWeightedCorrectionAfterAbsorberChoices rstar d hd mAbs aAbs bAbs αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs) ∧
      ∀(aLoad εR εH:ℝ),0<aLoad→aLoad≤a→0<εR→0<εH→
      ∀χinner χdeep χone χtwo χcut:ℝ,0<χinner→0<χdeep→0<χone→0<χtwo→0<χcut→
        OrdinaryDeepRowsCutsAfterParameters mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
          aLoad ε ξdeep b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap :=by
  obtain ⟨t,eEvent,hEvent,cap,ht,hevent,hhevent,hcap,hebound,hhbound,hselect⟩:=
    ordinary_deep_cap_before_load_choice mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep hdeep
      ε ξdeep b Bweight ηHub Kdom eParent hParent hε hε1 hεa hερ hξ hK hKdom hb hB he hh
  let capChosen:=min (cap*ε/1000) capExtra
  have hcapChosen:0<capChosen:=by dsimp [capChosen]; positivity
  obtain ⟨ξedit,hξedit,hξcap,hξlist,hξmatch,hcolumns⟩:=ordinary_early_uniform_columns_choose_smaller
    d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace capChosen hcapChosen hcolumns
  obtain ⟨ξAbs,hξAbs,hξAbscap,hξAbsh,hcorr⟩:=ordinary_correction_rate_before_absorber_under_cap
    rstar d hd αcorr pstar ω δAbs hAbs εabs εv (2*((3*d:ℕ):ℝ)) capChosen hcorr (by positivity) hcapChosen
  exact ⟨t,eEvent,hEvent,cap,ξedit,ξAbs,ht,hevent,hhevent,hcap,hebound,hhbound,
    hξedit,hξcap.trans (min_le_left _ _),hξcap.trans (min_le_right _ _),hξlist,hξmatch,hcolumns,
    hξAbs,hξAbscap.trans (min_le_left _ _),hξAbscap.trans (min_le_right _ _),hξAbsh,hcorr,hselect⟩
end Oberwolfach
