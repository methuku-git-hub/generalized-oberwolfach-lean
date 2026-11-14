module

public import Oberwolfach.OrdinaryTriangleOuterHubNumericInputs

@[expose] public section
/-! From the early outer hub choice, select its numeric weights together
with the matching and correction rates before the failure allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_common_rates_from_outer_hub_choice
    (d mMatch:ℕ) (hd:2≤d) (α ρ₀ pmin κ c C:ℝ) (htri:OrdinaryTriangleHubEarlyBeforeFailure α ρ₀ pmin κ c C)
    (aLoad ε:ℝ) (haLoad:0<aLoad) (haκ:aLoad≤κ) (hε:0<ε) (hε1:ε<1/4) (hεκ:ε≤κ) (hερ:ε≤ρ₀/16)
    (capξ ηHub Kdom ηbal ζlimit:ℝ) (hα:0<α) (hκ:0<κ) (hcapξ:0<capξ) (hηHub:0<ηHub) (hηbal:0<ηbal) (hζlimit:0<ζlimit)
    (hc:0<c) (hC:0<C) (hpmin:0<pmin)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (buffer:ℕ) (hbuffer:2≤buffer)
    (lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace:ℝ)
    (hcolumns:OrdinaryEarlyUniformColumnsBeforeAbsorberShape d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace)
    (αcorr pstar ω δAbs hAbs εabs εv capExtra:ℝ) (hExtra:0<capExtra)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly 3 αcorr pstar ω δAbs hAbs εabs εv):
    ∃b Bweight ξdeep t ζ δ δcap rate ξedit ξAbs:ℝ,
      0<b ∧ b≤c ∧ 0<Bweight ∧ (4*C/pmin^(3*2+1))*Kdom^2≤Bweight ∧
      0<ξdeep ∧ ξdeep≤capξ ∧
      (∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤κ ∧ β≤capξ ∧ β≤betaCap ∧ ξdeep+2*β<ηHub) ∧
      0<t ∧ 0<ζ ∧ ζ≤ζlimit ∧ 0<δ ∧ δ≤α ∧ 0<δcap ∧ δcap≤ζ/2 ∧ 0<rate ∧
      OrdinaryVortexBufferedTraceCapCostWitness ε ρ₀ α pmin pmin ηbal ζ δ δcap rate d buffer ∧
      0<ξedit ∧ ξedit≤δcap*ε/1000 ∧ ξedit≤capExtra ∧ ξedit≤bList/8 ∧ ξedit≤bMatch ∧
      OrdinaryEarlyUniformColumnsAtRate d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace ξedit ∧
      0<ξAbs ∧ ξAbs≤δcap*ε/1000 ∧ ξAbs≤capExtra ∧ ξAbs≤hAbs/100 ∧
      (∀mAbs:ℕ,∃aAbs bAbs:ℕ,OrdinaryWeightedCorrectionAfterAbsorberChoices 3 d hd mAbs aAbs bAbs αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs) ∧
      OrdinaryTriangleHubAfterCapBeforeFailure d hd α ρ₀ pmin κ aLoad ε ξdeep b Bweight ηHub δ δcap :=by
  obtain ⟨b,Bweight,hb,hbc,hB,hBbound⟩:=ordinary_triangle_outer_hub_numeric_inputs c C pmin Kdom hc hC hpmin
  obtain ⟨ξdeep,t,ζ,δ,δcap,rate,ξedit,ξAbs,hξ,hξcap,hβ,ht,hζ,hζlimit',hδ,hδα,hδcap,hδζ,hrate,htrace,
    hξedit,hξeditscale,hξeditextra,hξlist,hξmatch,hcolumns',hξAbs,hξAbsscale,hξAbsextra,hξAbsh,hcorr',hselect⟩:=
      ordinary_triangle_common_rates_late_vortex_error d mMatch hd α ρ₀ pmin κ c C htri aLoad ε haLoad haκ hε hε1 hεκ hερ
        capξ b Bweight ηHub Kdom ηbal ζlimit hα hκ hcapξ hηHub hηbal hζlimit hKdom hbc hBbound buffer hbuffer
        lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace hcolumns
        αcorr pstar ω δAbs hAbs εabs εv capExtra hExtra hcorr
  exact ⟨b,Bweight,ξdeep,t,ζ,δ,δcap,rate,ξedit,ξAbs,hb,hbc,hB,hBbound,hξ,hξcap,hβ,ht,hζ,hζlimit',hδ,hδα,hδcap,hδζ,hrate,htrace,
    hξedit,hξeditscale,hξeditextra,hξlist,hξmatch,hcolumns',hξAbs,hξAbsscale,hξAbsextra,hξAbsh,hcorr',hselect⟩
end Oberwolfach
