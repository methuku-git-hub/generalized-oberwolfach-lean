module

public import Oberwolfach.OrdinaryTriangleParentRateBothCaps

@[expose] public section
/-! Refine the reference rate and choose one positive sample tolerance
before selecting the protected-balance and fine-cover rates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_parent_rate_and_sample_tolerance
    (βH ηH B ω pstar βparent εparent ζparent rateRoot lamInner δend ε:ℝ) (N₀:ℕ)
    (hN₀:1≤N₀) (hroot:0<rateRoot) (hlam:0<lamInner) (hδ:0<δend) (hε:0<ε)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζparent rateRoot N₀)
    (capHub ζlimit:ℝ) (hHub:0<capHub) (hLimit:0<ζlimit):
    ∃rateParent ζcert:ℝ,0<rateParent ∧ rateParent≤rateRoot ∧ rateParent≤lamInner*ε/4 ∧ rateParent≤δend*ε/8 ∧
      OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζparent rateParent N₀ ∧
      0<ζcert ∧ ζcert≤rateParent ∧ ζcert≤capHub ∧ ζcert≤ζlimit :=by
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
  exact ⟨rateParent,ζcert,hrate,hrateRoot,hrateInner,hrateEnd,hscale',hζ,hζrate,hζhub,hζlimit⟩
end Oberwolfach
