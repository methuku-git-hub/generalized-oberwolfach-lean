module

public import Oberwolfach.OrdinaryTriangleParentRootScaleChoice

@[expose] public section
/-! A later positive numerical cap can shrink the already selected edit
rate without changing the parent reference, cutoffs or other parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_edit_scale_rate_mono
    (βH ηH B ω pstar βparent εparent ζ rate rate':ℝ) (N₀:ℕ) (hN₀:1≤N₀)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζ rate N₀)
    (hrate:rate'≤rate):
    OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζ rate' N₀ :=by
  obtain ⟨hdegree,hbound⟩:=hscale
  refine ⟨hdegree,?_⟩
  intro N U L hN hU hL hLrate
  have hN0:0≤N:=by
    have hh:(0:ℝ)≤N₀:=by positivity
    exact hh.trans hN
  exact hbound N U L hN hU hL (hLrate.trans (mul_le_mul_of_nonneg_right hrate hN0))

theorem ordinary_triangle_edit_scale_choose_below
    (βH ηH B ω pstar βparent εparent ζ rate cap:ℝ) (N₀:ℕ) (hN₀:1≤N₀)
    (hrate:0<rate) (hcap:0<cap)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζ rate N₀):
    ∃rate':ℝ,0<rate' ∧ rate'≤rate ∧ rate'≤cap ∧
      OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζ rate' N₀ :=by
  let rate':=min rate cap
  have hp:0<rate':=by dsimp [rate'];positivity
  have hr:rate'≤rate:=min_le_left _ _
  exact ⟨rate',hp,hr,min_le_right _ _,ordinary_triangle_edit_scale_rate_mono
    βH ηH B ω pstar βparent εparent ζ rate rate' N₀ hN₀ hscale hr⟩
end Oberwolfach
