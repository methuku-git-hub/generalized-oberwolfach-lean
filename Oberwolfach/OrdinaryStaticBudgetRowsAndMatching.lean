module

public import Oberwolfach.OrdinaryFixedEventBudgetedMatching
public import Oberwolfach.OrdinaryTriangleCommonRowToleranceChoice

@[expose] public section
/-! Choose the placement budget, common row tolerance and fixed matching
rates before the failure allowances of the selected static wheel event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach

theorem ordinary_static_budget_rows_and_matching
    (L rstar m k dMin:ℕ) (hr:3≤rstar)
    (βfreq ρ₀ α γList capInner θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hρ1:ρ₀≤1) (hα:0<α) (hθhost:1/2≤θhost)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly)
    (ε cap ηedit ζcert capOriginal αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (hε:0<ε) (hcap:0<cap) (hηedit:0<ηedit) (hζcert:0<ζcert) (hOriginal:0<capOriginal)
    (δInitial δDeep δedit εsample γgeom δend δcap εrows:ℝ)
    (hInitial:0<δInitial) (hDeep:0<δDeep) (hEdit:0<δedit) (hSample:0<εsample)
    (hγ:0<γgeom) (hEnd:0<δend) (hδcap:0<δcap) (hRows:0<εrows)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ω δAbs hAbs εabs εv)
    (hm:7≤m) (hεearly:ε≤εearly) (habs:ε≤εabs) (hv:ε≤εv)
    (hEarly:OrdinaryPlacementEarlyRateData (α/2) ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace εearly dMin):
    ∃ηBudget capEdit row:ℝ,0<ηBudget ∧ ηBudget≤ηedit ∧ 15*ηBudget≤ζcert*ε/2 ∧
      0<capEdit ∧ capEdit≤capOriginal ∧ capEdit≤ηBudget ∧
      0<row ∧ row≤δInitial ∧ row≤δDeep ∧ row≤δedit ∧ row≤εsample ∧
      row≤γgeom/1000 ∧ row≤δend/4 ∧ 2*row≤εrows ∧ row≤δcap ∧
    ∃d:ℕ,∃hd:2≤d,∃ξedit ξAbs:ℝ, ξedit≤cap ∧ ξAbs≤cap ∧
      OrdinaryOriginalPreSampleFixedJointRatesAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs ∧
      ∀(βv:ℝ) (mv:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ),
        0<ζ→0<χpair→0<χlist→0<χbal→0<χbd→0<χnbr→0<χpairR→0<χpath→
        0<χlocal→0<χglobal→0<χhub→0<χcol→
        OrdinaryOriginalPreSampleJointThresholdsSeparateListsAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
          hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv
          mv (2*mv) 10 ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol ξedit ξAbs βv :=by
  obtain ⟨ηBudget,capEdit,hBudget,hBudgetη,hsmall,hEditCap,hOriginal',hEditBudget,d,hd,ξedit,ξAbs,hξcap,hξAbscap,hjoint,hthresholds⟩:=
    ordinary_fixed_event_budgeted_matching L rstar m k dMin hr βfreq ρ₀ α γList capInner θhost
      hβfreq hβ1 hρ₀ hρ1 hα hθhost βPlace lamPlace ζPlace εearly hTail
      ε cap ηedit ζcert capOriginal αcorr pstar ω δAbs hAbs εabs εv hε hcap hηedit hζcert hOriginal hcorr hm hεearly habs hv hEarly
  obtain ⟨row,hrow,hI,hD,hE,hS,hG,hEnd',hRows',hCap⟩:=
    ordinary_triangle_common_row_tolerance_choice δInitial δDeep δedit εsample γgeom δend εrows δcap
      hInitial hDeep hEdit hSample hγ hEnd hRows hδcap
  exact ⟨ηBudget,capEdit,row,hBudget,hBudgetη,hsmall,hEditCap,hOriginal',hEditBudget,hrow,hI,hD,hE,hS,hG,hEnd',hRows',hCap,
    d,hd,ξedit,ξAbs,hξcap,hξAbscap,hjoint,hthresholds⟩
end Oberwolfach
