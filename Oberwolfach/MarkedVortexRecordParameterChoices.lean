module

public import Mathlib.Tactic

@[expose] public section

/-! Select the vortex ratio before the quantities depending on it, then
select its quality parameter after the sampled-event and level tolerances. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_vortex_record_parameter_choices
    (ε₀ εAbs:ℝ) (hε₀:0<ε₀) (hεAbs:0<εAbs) (hε₀small:ε₀≤1/8):
    ∃ ε:ℝ,0<ε ∧ ε≤ε₀ ∧ ε≤εAbs ∧ ε<1/4 ∧
    ∀ βmax κ α x:ℝ,0<βmax→0<κ→0<α→0<x→
      ∃ β:ℝ,0<β ∧ β≤βmax ∧ β≤κ/16 ∧ β≤1/4 ∧ β≤α/8 ∧
        β≤3*α/40 ∧ β≤3/20 ∧ β≤κ ∧ β≤x := by
  let ε:=min ε₀ εAbs / 2
  have hε:0<ε := by dsimp [ε];positivity
  have he₀:ε≤ε₀ := by have h:=min_le_left ε₀ εAbs;dsimp [ε];linarith
  have heAbs:ε≤εAbs := by have h:=min_le_right ε₀ εAbs;dsimp [ε];linarith
  refine ⟨ε,hε,he₀,heAbs,by linarith,?_⟩
  intro βmax κ α x hb hk ha hx
  let β:=min βmax (min (κ/16) (min (1/4) (min (α/8) (min (3*α/40) (min (3/20) x)))))
  have hβ:0<β := by dsimp [β];positivity
  have h1:β≤βmax := min_le_left _ _
  have h2:β≤κ/16 := (min_le_right _ _).trans (min_le_left _ _)
  have h3:β≤(1:ℝ)/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4:β≤α/8 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h5:β≤3*α/40 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have h6:β≤(3:ℝ)/20 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have h7:β≤x := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  exact ⟨β,hβ,h1,h2,h3,h4,h5,h6,by linarith,h7⟩
end Oberwolfach
