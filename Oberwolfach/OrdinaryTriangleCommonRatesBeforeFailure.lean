module

public import Oberwolfach.OrdinaryTriangleHubCapBeforeFailureChoice
public import Oberwolfach.OrdinaryEarlyUniformColumnsChooseSmaller
public import Oberwolfach.OrdinaryCorrectionRateBeforeAbsorberUnderCap

@[expose] public section
/-! Choose triangle trace, target edit and correction rates before all
failure allowances and before absorber sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_common_rates_before_failure
    (d mMatch:ℕ) (hd:2≤d) (α ρ₀ pmin κ c C:ℝ) (htri:OrdinaryTriangleHubEarlyBeforeFailure α ρ₀ pmin κ c C)
    (aLoad ε:ℝ) (haLoad:0<aLoad) (haκ:aLoad≤κ) (hε:0<ε) (hε1:ε<1/4) (hεκ:ε≤κ) (hερ:ε≤ρ₀/16)
    (ξdeep b Bweight ηHub Kdom ηbal ζlimit:ℝ) (hξ:0<ξdeep) (hηbal:0<ηbal) (hζlimit:0<ζlimit)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (hb:b≤c)
    (hB:(4*C/pmin^(3*2+1))*Kdom^2≤Bweight) (buffer:ℕ) (hbuffer:2≤buffer)
    (lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace:ℝ)
    (hcolumns:OrdinaryEarlyUniformColumnsBeforeAbsorberShape d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace)
    (αcorr pstar ω δAbs hAbs εabs εv capExtra:ℝ) (hExtra:0<capExtra)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly 3 αcorr pstar ω δAbs hAbs εabs εv):
    ∃t ζ δ δcap rate ξedit ξAbs:ℝ,
      0<t ∧ 0<ζ ∧ ζ≤ζlimit ∧ 0<δ ∧ δ≤α ∧ 0<δcap ∧ δcap≤ζ/2 ∧ 0<rate ∧
      OrdinaryVortexBufferedTraceCapCostWitness ε ρ₀ α pmin pmin ηbal ζ δ δcap rate d buffer ∧
      0<ξedit ∧ ξedit≤δcap*ε/1000 ∧ ξedit≤capExtra ∧ ξedit≤bList/8 ∧ ξedit≤bMatch ∧
      OrdinaryEarlyUniformColumnsAtRate d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace ξedit ∧
      0<ξAbs ∧ ξAbs≤δcap*ε/1000 ∧ ξAbs≤capExtra ∧ ξAbs≤hAbs/100 ∧
      (∀mAbs:ℕ,∃aAbs bAbs:ℕ,OrdinaryWeightedCorrectionAfterAbsorberChoices 3 d hd mAbs aAbs bAbs αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs) ∧
      OrdinaryTriangleHubAfterCapBeforeFailure d hd α ρ₀ pmin κ aLoad ε ξdeep b Bweight ηHub δ δcap :=by
  obtain ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlimit',hδ,hδα,hδcap,hδζ,hrate,htrace,hselect⟩:=
    ordinary_triangle_hub_cap_before_failure_choice α ρ₀ pmin κ c C htri aLoad ε haLoad haκ hε hε1 hεκ hερ
      d hd ξdeep b Bweight ηHub Kdom ηbal ζlimit hξ hηbal hζlimit hKdom hb hB buffer hbuffer
  let capChosen:=min (δcap*ε/1000) capExtra
  have hcapChosen:0<capChosen:=by dsimp [capChosen]; positivity
  obtain ⟨ξedit,hξedit,hξcap,hξlist,hξmatch,hcolumns⟩:=ordinary_early_uniform_columns_choose_smaller
    d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace capChosen hcapChosen hcolumns
  obtain ⟨ξAbs,hξAbs,hξAbscap,hξAbsh,hcorr⟩:=ordinary_correction_rate_before_absorber_under_cap
    3 d hd αcorr pstar ω δAbs hAbs εabs εv (2*((3*d:ℕ):ℝ)) capChosen hcorr (by positivity) hcapChosen
  exact ⟨t,ζ,δ,δcap,rate,ξedit,ξAbs,ht,hζ,hζlimit',hδ,hδα,hδcap,hδζ,hrate,htrace,
    hξedit,hξcap.trans (min_le_left _ _),hξcap.trans (min_le_right _ _),hξlist,hξmatch,hcolumns,
    hξAbs,hξAbscap.trans (min_le_left _ _),hξAbscap.trans (min_le_right _ _),hξAbsh,hcorr,hselect⟩
end Oberwolfach
