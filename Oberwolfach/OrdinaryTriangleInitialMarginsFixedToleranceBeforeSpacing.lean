module

public import Oberwolfach.OrdinaryPreSampleForInitialPlacementBudget
public import Oberwolfach.OrdinaryInitialMatchingMarginsAt

@[expose] public section
/-! With the sample tolerance already fixed, choose initial matching margins
and its placement budget before the matching spacing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_initial_margins_fixed_tolerance_before_spacing
    (ρ₀ α pmin hmin cInitial:ℝ)
    (hInitial:∀ε:ℝ,0<ε→ε<1/4→∀bal:ℝ,0<bal→
      ∃δ η:ℝ,0<δ ∧ δ≤α ∧ δ≤bal ∧ 0<η ∧
      ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δ→∃m₀ N:ℕ,1≤m₀ ∧
        OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε bal cInitial δ η β d m₀ N)
    (ε bal ζcert capOriginal:ℝ) (hε:0<ε) (hεsmall:ε<1/4) (hbal:0<bal) (hζ:0<ζcert) (hOriginal:0<capOriginal)
    (L rstar m k dMin:ℕ) (βfreq αOriginal γList capInner θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ αOriginal γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly):
    ∃δedit ηedit ηBudget capChosen:ℝ,0<δedit ∧ δedit≤α ∧ δedit≤bal ∧ 0<ηedit ∧
      0<ηBudget ∧ ηBudget≤ηedit ∧ 15*ηBudget≤ζcert*ε/2 ∧
      0<capChosen ∧ capChosen≤capOriginal ∧ capChosen≤ηBudget ∧
      ∃d:ℕ,∃hd:2≤d,
        OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ αOriginal γList capInner capChosen θhost
          hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly ∧
        ∀β:ℝ,0≤β→β≤1/4→β≤δedit→∃m₀ N:ℕ,1≤m₀ ∧
          OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε bal cInitial δedit ηedit β d m₀ N :=by
  obtain ⟨δedit,ηedit,hδ,hδα,hδbal,hη,hmargins⟩:=hInitial ε hε hεsmall bal hbal
  obtain ⟨ηBudget,capChosen,hBudget,hBudgetη,hsmall,hChosen,hcap,hcapBudget,d,hd,hpre⟩:=
    ordinary_presample_for_initial_placement_budget L rstar m k dMin βfreq ρ₀ αOriginal γList capInner θhost
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly hTail capOriginal ηedit ζcert ε hOriginal hη hζ hε
  exact ⟨δedit,ηedit,ηBudget,capChosen,hδ,hδα,hδbal,hη,hBudget,hBudgetη,hsmall,hChosen,hcap,hcapBudget,d,hd,hpre,hmargins d⟩
end Oberwolfach
