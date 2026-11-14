module

public import Oberwolfach.FiniteWindowRecentCost

@[expose] public section
/-! Uniform component bounds imply the recent-level cost bound used by the
buffered trace. Each cost uses its own parent size. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem finite_window_coverdown_recipe
    (J:Finset ℕ) (parent cost ν η ρ:ℕ→ℝ) (rate C:ℝ)
    (hparent:∀j∈J,0≤parent j) (hrate:0≤rate) (hC:0≤C)
    (hν:∀j∈J,0≤ν j ∧ ν j≤rate*parent j)
    (hη:∀j∈J,0≤η j ∧ η j≤rate*parent j)
    (hρ:∀j∈J,0≤ρ j ∧ ρ j≤rate)
    (hcost:∀j∈J,cost j=ν j+η j+(2*(ρ j*parent j)+C)):
    ∀j∈J,0≤cost j ∧ cost j≤4*rate*parent j+C := by
  intro j hj
  have hp:=hparent j hj
  have hn:=hν j hj
  have he:=hη j hj
  have hr:=hρ j hj
  have hm:=mul_le_mul_of_nonneg_right hr.2 hp
  rw [hcost j hj]
  constructor
  · nlinarith [mul_nonneg hr.1 hp]
  · nlinarith
end Oberwolfach
