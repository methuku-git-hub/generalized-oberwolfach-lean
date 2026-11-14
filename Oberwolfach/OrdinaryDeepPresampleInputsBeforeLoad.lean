module

public import Oberwolfach.OrdinaryDeepCostAndScaledRatesBeforeLoad
public import Oberwolfach.OrdinaryDeepWeightChoicesBeforeLoad
public import Oberwolfach.OrdinaryDeepSpacingErrorBeforeLateCap
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

theorem ordinary_deep_presample_inputs_before_load
    (rstar mWheel Kdeep d mMatch:ℕ) (hd:2≤d)
    (αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (hdeep:OrdinaryDeepRowsCutsEarlyBeforeLoad mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep)
    (ε ηHub eParent hParent capξ capWeight:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεa:ε≤a) (hερ:ε≤ρ₀/16)
    (hρ₀:0<ρ₀) (hα:0<αdeep) (hε₀:0<ε₀) (hηHub:0<ηHub)
    (hcapξ:0<capξ) (hcapWeight:0<capWeight) (ha:0<a) (hc:0<c) (hC:0<C) (hpmin:0<pmin)
    (he:0<eParent) (hh:0<hParent)
    (lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace:ℝ)
    (hcolumns:OrdinaryEarlyUniformColumnsBeforeAbsorberShape d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace)
    (αcorr pstar ω δAbs hAbs εabs εv capExtra:ℝ) (hExtra:0<capExtra)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ω δAbs hAbs εabs εv):
    ∃ξdeep b Kdom Bweight:ℝ,
      0<ξdeep ∧ ξdeep≤capξ ∧ 0<b ∧ b≤c ∧ b≤capWeight ∧ 0<Kdom ∧ 0<Bweight ∧
      2/ε≤Kdom ∧ 1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom ∧
      (4*C/pmin^(3*mWheel+1))*Kdom^mWheel≤Bweight ∧
      (∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤αdeep/8 ∧ β≤ε₀ ∧ β≤capξ ∧ β≤betaCap ∧ ξdeep+2*β<ηHub) ∧
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
  obtain ⟨ξdeep,hξdeep,hξcap,hβchoose⟩:=
    ordinary_deep_spacing_error_before_late_cap αdeep ε₀ capξ ηHub hα hε₀ hcapξ hηHub
  obtain ⟨b,Kdom,Bweight,hb,hbc,hbcap,hKpos,hBpos,hK,hKdom,hB⟩:=
    ordinary_deep_weight_choices_before_load mWheel a c capWeight ε ρ₀ pmin C
      ha hc hcapWeight hε hρ₀ hpmin hC
  refine ⟨ξdeep,b,Kdom,Bweight,hξdeep,hξcap,hb,hbc,hbcap,hKpos,hBpos,hK,hKdom,hB,hβchoose,?_⟩
  exact ordinary_deep_cost_and_scaled_rates_before_load rstar mWheel Kdeep d mMatch hd
      αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep hdeep
      ε ξdeep b Bweight ηHub Kdom eParent hParent hε hε1 hεa hερ hρ₀ hξdeep hK hKdom hbc hB he hh
      lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace hcolumns
      αcorr pstar ω δAbs hAbs εabs εv capExtra hExtra hcorr
end Oberwolfach
