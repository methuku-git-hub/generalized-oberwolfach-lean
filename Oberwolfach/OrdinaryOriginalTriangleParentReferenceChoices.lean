module

public import Oberwolfach.OrdinaryTriangleParentReferenceChoices

@[expose] public section
/-! Original frequency, density and feasible host margins supply triangle
parent and reference choices for any later spacing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_original_triangle_parent_reference_choices
    (βfreq ρ₀ α ηP:ℝ)
    (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1) (hα:0<α) (hη:0<ηP)
    (hmargin:α/2≤1/2 ∧ max (1/2) (cycleThreshold 3)+(α/2)/2≤1):
    let pstar:=ρ₀*(βfreq/200)/2
    ∀d:ℕ,∀hd:2≤d,
      OrdinaryTriangleParentReferenceChoices d hd (α/2) ρ₀ pstar ηP (by positivity) (by positivity) :=by
  intro pstar d hd
  have hp:0<pstar:=by dsimp [pstar];positivity
  have hs:0<βfreq/200:=by positivity
  have hs1:βfreq/200≤1:=by linarith
  have hp1:pstar≤1:=by
    have hh:=mul_le_mul_of_nonneg_right hρ1 hs.le
    have hm:ρ₀*(βfreq/200)≤1:=by nlinarith [hh,hs1]
    dsimp [pstar]
    nlinarith
  exact ordinary_triangle_reference_event_hierarchy d hd (α/2) ρ₀ pstar ηP (by positivity) hmargin.1 hmargin.2 hρ hp hp1 hη
end Oberwolfach
