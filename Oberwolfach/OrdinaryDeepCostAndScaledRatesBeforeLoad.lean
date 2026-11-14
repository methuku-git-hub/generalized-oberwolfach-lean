module

public import Oberwolfach.OrdinaryDeepScaledRatesBeforeLoad
public import Oberwolfach.OrdinarySelectedCostRate
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

theorem ordinary_deep_cost_and_scaled_rates_before_load
    (rstar mWheel Kdeep d mMatch:ℕ) (hd:2≤d)
    (αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (hdeep:OrdinaryDeepRowsCutsEarlyBeforeLoad mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep)
    (ε ξdeep b Bweight ηHub Kdom eParent hParent:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεa:ε≤a) (hερ:ε≤ρ₀/16)
    (hρ₀:0<ρ₀) (hξ:0<ξdeep) (hK:2/ε≤Kdom) (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (hb:b≤c)
    (hB:(4*C/pmin^(3*mWheel+1))*Kdom^mWheel≤Bweight) (he:0<eParent) (hh:0<hParent)
    (lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace:ℝ)
    (hcolumns:OrdinaryEarlyUniformColumnsBeforeAbsorberShape d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace)
    (αcorr pstar ω δAbs hAbs εabs εv capExtra:ℝ) (hExtra:0<capExtra)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ω δAbs hAbs εabs εv):
    ∃t eEvent hEvent cap ξedit ξAbs costRate:ℝ,
      0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧ eEvent≤eParent ∧ hEvent≤hParent ∧
      0<costRate ∧ OrdinarySelectedCostRate ε ρ₀ cap d costRate ∧
      0<ξedit ∧ ξedit≤cap*ε/1000 ∧ ξedit≤capExtra ∧ ξedit≤bList/8 ∧ ξedit≤bMatch ∧
      OrdinaryEarlyUniformColumnsAtRate d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace ξedit ∧
      0<ξAbs ∧ ξAbs≤cap*ε/1000 ∧ ξAbs≤capExtra ∧ ξAbs≤hAbs/100 ∧
      (∀mAbs:ℕ,∃aAbs bAbs:ℕ,OrdinaryWeightedCorrectionAfterAbsorberChoices rstar d hd mAbs aAbs bAbs αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs) ∧
      ∀(aLoad εR εH:ℝ),0<aLoad→aLoad≤a→0<εR→0<εH→
      ∀χinner χdeep χone χtwo χcut:ℝ,0<χinner→0<χdeep→0<χone→0<χtwo→0<χcut→
        OrdinaryDeepRowsCutsAfterParameters mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
          aLoad ε ξdeep b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap :=by
  obtain ⟨t,eEvent,hEvent,cap,ξedit,ξAbs,ht,hevent,hhevent,hcap,hebound,hhbound,
    hξedit,hξcap,hξextra,hξlist,hξmatch,hcolumns,hξAbs,hξAbscap,hξAbsextra,hξAbsh,hcorr,hselect⟩:=
    ordinary_deep_scaled_rates_before_load rstar mWheel Kdeep d mMatch hd
      αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep hdeep
      ε ξdeep b Bweight ηHub Kdom eParent hParent hε hε1 hεa hερ hξ hK hKdom hb hB he hh
      lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace hcolumns
      αcorr pstar ω δAbs hAbs εabs εv capExtra hExtra hcorr
  obtain ⟨costRate,hcost,hcostproperty⟩:=ordinary_selected_cost_rate_choice ε ρ₀ cap d hε hε1 hρ₀ hcap
  exact ⟨t,eEvent,hEvent,cap,ξedit,ξAbs,costRate,ht,hevent,hhevent,hcap,hebound,hhbound,
    hcost,hcostproperty,hξedit,hξcap,hξextra,hξlist,hξmatch,hcolumns,
    hξAbs,hξAbscap,hξAbsextra,hξAbsh,hcorr,hselect⟩
end Oberwolfach
