module

public import Oberwolfach.OrdinaryTriangleParentRateBothCaps
public import Oberwolfach.OrdinaryPreSampleForInitialPlacementBudget

@[expose] public section
/-! Refine the parent edit rate, choose its sample tolerance and initial
matching budget, then select the matching spacing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_rate_tolerance_placement_before_spacing
    (βH ηH B ω pstar βparent εparent ζparent rateRoot lamInner δend ε:ℝ) (N₀:ℕ)
    (hN₀:1≤N₀) (hroot:0<rateRoot) (hlam:0<lamInner) (hδ:0<δend) (hε:0<ε)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζparent rateRoot N₀)
    (capHub ζlimit ηedit capOriginal:ℝ) (hHub:0<capHub) (hLimit:0<ζlimit)
    (hη:0<ηedit) (hOriginal:0<capOriginal)
    (L rstar m k dMin:ℕ) (βfreq ρ₀ α γList capInner θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly):
    ∃rateParent ζcert ηBudget capChosen:ℝ,
      0<rateParent ∧ rateParent≤rateRoot ∧ rateParent≤lamInner*ε/4 ∧ rateParent≤δend*ε/8 ∧
      OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζparent rateParent N₀ ∧
      0<ζcert ∧ ζcert≤rateParent ∧ ζcert≤capHub ∧ ζcert≤ζlimit ∧
      0<ηBudget ∧ ηBudget≤ηedit ∧ 15*ηBudget≤ζcert*ε/2 ∧
      0<capChosen ∧ capChosen≤capOriginal ∧ capChosen≤ηBudget ∧
      ∃d:ℕ,∃hd:2≤d,
        OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capChosen θhost
          hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly :=by
  obtain ⟨rateParent,hrate,hrateRoot,hrateInner,hrateEnd,hscale'⟩:=
    ordinary_triangle_parent_rate_both_caps βH ηH B ω pstar βparent εparent ζparent rateRoot lamInner δend ε N₀
      hN₀ hroot hlam hδ hε hscale
  let ζcert:ℝ:=min rateParent (min capHub ζlimit)/2
  have hζ:0<ζcert:=by dsimp [ζcert];positivity
  have hζrate:ζcert≤rateParent:=by dsimp [ζcert];have h:=min_le_left rateParent (min capHub ζlimit);linarith
  have hζhub:ζcert≤capHub:=by
    have h:min rateParent (min capHub ζlimit)≤capHub:=(min_le_right _ _).trans (min_le_left _ _)
    dsimp [ζcert];linarith
  have hζlimit:ζcert≤ζlimit:=by
    have h:min rateParent (min capHub ζlimit)≤ζlimit:=(min_le_right _ _).trans (min_le_right _ _)
    dsimp [ζcert];linarith
  obtain ⟨ηBudget,capChosen,hBudget,hBudgetη,hsmall,hChosen,hcap,hcapBudget,d,hd,hpre⟩:=
    ordinary_presample_for_initial_placement_budget L rstar m k dMin βfreq ρ₀ α γList capInner θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly hTail capOriginal ηedit ζcert ε hOriginal hη hζ hε
  exact ⟨rateParent,ζcert,ηBudget,capChosen,hrate,hrateRoot,hrateInner,hrateEnd,hscale',
    hζ,hζrate,hζhub,hζlimit,hBudget,hBudgetη,hsmall,hChosen,hcap,hcapBudget,d,hd,hpre⟩
end Oberwolfach
