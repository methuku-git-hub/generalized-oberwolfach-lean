module

public import Oberwolfach.OrdinaryTriangleEditScaleRateRefinement

@[expose] public section
/-! The same parent edit rate can meet the inner-factor and pairing bounds
while preserving the selected reference and its original parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_parent_rate_both_caps
    (βH ηH B ω pstar βparent εparent ζ rateRoot lamInner δend ε:ℝ) (N₀:ℕ)
    (hN₀:1≤N₀) (hroot:0<rateRoot) (hlam:0<lamInner) (hδ:0<δend) (hε:0<ε)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζ rateRoot N₀):
    ∃rateParent:ℝ,0<rateParent ∧ rateParent≤rateRoot ∧ rateParent≤lamInner*ε/4 ∧
      rateParent≤δend*ε/8 ∧
      OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζ rateParent N₀ :=by
  let cap:=min (lamInner*ε/4) (δend*ε/8)
  have hcap:0<cap:=by dsimp [cap];positivity
  obtain ⟨rateParent,hpos,hroot',hcap',hscale'⟩:=ordinary_triangle_edit_scale_choose_below
    βH ηH B ω pstar βparent εparent ζ rateRoot cap N₀ hN₀ hroot hcap hscale
  exact ⟨rateParent,hpos,hroot',hcap'.trans (min_le_left _ _),hcap'.trans (min_le_right _ _),hscale'⟩
end Oberwolfach
