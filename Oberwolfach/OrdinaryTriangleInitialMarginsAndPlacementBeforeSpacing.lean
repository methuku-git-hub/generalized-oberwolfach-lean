module

public import Oberwolfach.OrdinaryTriangleRateTolerancePlacementBeforeSpacing
public import Oberwolfach.OrdinaryInitialMatchingMarginsAt

@[expose] public section
/-! Select the initial matching margins and the edit budget before choosing
spacing, while retaining the refined triangle parent rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_initial_margins_and_placement_before_spacing
    (ρ₀ α pmin hmin cInitial:ℝ)
    (hInitial:∀ε:ℝ,0<ε→ε<1/4→∀bal:ℝ,0<bal→
      ∃δ η:ℝ,0<δ ∧ δ≤α ∧ δ≤bal ∧ 0<η ∧
      ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δ→∃m₀ N:ℕ,1≤m₀ ∧
        OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε bal cInitial δ η β d m₀ N)
    (βH ηH B ω pstar βparent εparent ζparent rateRoot lamInner δend ε:ℝ) (N₀:ℕ)
    (hN₀:1≤N₀) (hroot:0<rateRoot) (hlam:0<lamInner) (hδ:0<δend) (hε:0<ε) (hεsmall:ε<1/4)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζparent rateRoot N₀)
    (bal capHub ζlimit capOriginal:ℝ) (hbal:0<bal) (hHub:0<capHub) (hLimit:0<ζlimit) (hOriginal:0<capOriginal)
    (L rstar m k dMin:ℕ) (βfreq αOriginal γList capInner θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ αOriginal γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly):
    ∃δedit ηedit rateParent ζcert ηBudget capChosen:ℝ,
      0<δedit ∧ δedit≤α ∧ δedit≤bal ∧ 0<ηedit ∧
      0<rateParent ∧ rateParent≤rateRoot ∧ rateParent≤lamInner*ε/4 ∧ rateParent≤δend*ε/8 ∧
      OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζparent rateParent N₀ ∧
      0<ζcert ∧ ζcert≤rateParent ∧ ζcert≤capHub ∧ ζcert≤ζlimit ∧
      0<ηBudget ∧ ηBudget≤ηedit ∧ 15*ηBudget≤ζcert*ε/2 ∧
      0<capChosen ∧ capChosen≤capOriginal ∧ capChosen≤ηBudget ∧
      ∃d:ℕ,∃hd:2≤d,
        OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ αOriginal γList capInner capChosen θhost
          hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly ∧
        ∀β:ℝ,0≤β→β≤1/4→β≤δedit→∃m₀ N:ℕ,1≤m₀ ∧
          OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε bal cInitial δedit ηedit β d m₀ N :=by
  obtain ⟨δedit,ηedit,hδedit,hδα,hδbal,hηedit,hmargins⟩:=hInitial ε hε hεsmall bal hbal
  obtain ⟨rateParent,ζcert,ηBudget,capChosen,hrate,hrateRoot,hrateInner,hrateEnd,hscale',
      hζ,hζrate,hζhub,hζlimit,hBudget,hBudgetη,hsmall,hChosen,hcap,hcapBudget,d,hd,hpre⟩:=
    ordinary_triangle_rate_tolerance_placement_before_spacing βH ηH B ω pstar βparent εparent ζparent rateRoot lamInner δend ε N₀
      hN₀ hroot hlam hδ hε hscale capHub ζlimit ηedit capOriginal hHub hLimit hηedit hOriginal
      L rstar m k dMin βfreq ρ₀ αOriginal γList capInner θhost hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly hTail
  exact ⟨δedit,ηedit,rateParent,ζcert,ηBudget,capChosen,hδedit,hδα,hδbal,hηedit,
    hrate,hrateRoot,hrateInner,hrateEnd,hscale',hζ,hζrate,hζhub,hζlimit,hBudget,hBudgetη,hsmall,hChosen,hcap,hcapBudget,
    d,hd,hpre,hmargins d⟩
end Oberwolfach
