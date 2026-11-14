module

public import Oberwolfach.OrdinarySmallRootDensity

@[expose] public section
/-! A single positive slack meets both the pair-profile and common-hub margins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_long_absorber_slack_choice (h:ℕ) (α pmin smin ω:ℝ)
    (hα:0<α) (hp:0<pmin) (hs:0<smin) (hω:0<ω):
    ∃ β:ℝ,0<β ∧ β≤α*pmin^2*smin^2 ∧ β≤ω*smin^h/4 := by
  let β:=min (α*pmin^2*smin^2) (ω*smin^h/4)
  refine ⟨β,?_,min_le_left _ _,min_le_right _ _⟩
  dsimp [β]
  apply lt_min <;> positivity

theorem ordinary_triangle_absorber_slack_choice (h:ℕ) (α pmin smin ω:ℝ)
    (hα:0<α) (hp:0<pmin) (hs:0<smin) (hω:0<ω):
    ∃ β:ℝ,0<β ∧ β≤2*(min α (1/4))*pmin^4*smin^4 ∧ β≤ω*smin^h/4 := by
  let β:=min (2*(min α (1/4))*pmin^4*smin^4) (ω*smin^h/4)
  refine ⟨β,?_,min_le_left _ _,min_le_right _ _⟩
  dsimp [β]
  have hx:0<min α (1/4:ℝ):=lt_min hα (by norm_num)
  apply lt_min <;> positivity
end Oberwolfach
