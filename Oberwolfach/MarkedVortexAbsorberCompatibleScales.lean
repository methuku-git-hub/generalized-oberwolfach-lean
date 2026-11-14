module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! Vortex shrinkage and regularity tolerances can be chosen after the
absorber tolerance and the level weight margin. -/
set_option autoImplicit false
namespace Oberwolfach

theorem marked_vortex_absorber_compatible_scales
    (α βmax εBal εRef εAbs:ℝ) (hα:0<α) (hβmax:0<βmax)
    (hBal:0<εBal) (hRef:0<εRef) (hAbs:0<εAbs):
    ∃εQ βQ:ℝ,0<εQ ∧ εQ<1/4 ∧ εQ≤εAbs ∧
      0<βQ ∧ βQ≤1/4 ∧ βQ≤α/4 ∧ βQ≤βmax ∧ βQ≤εBal/4 ∧ βQ≤εRef/4 := by
  let εQ:=min (1/8:ℝ) (εAbs/2)
  let βQ:=min (1/8:ℝ) (min (α/4) (min βmax (min (εBal/4) (εRef/4))))
  have he:0<εQ:=by dsimp [εQ];positivity
  have hb:0<βQ:=by dsimp [βQ];positivity
  have he1:εQ≤1/8:=min_le_left _ _
  have hea:εQ≤εAbs/2:=min_le_right _ _
  have hb1:βQ≤1/8:=min_le_left _ _
  have hba:βQ≤α/4:=(min_le_right _ _).trans (min_le_left _ _)
  have hbb:βQ≤βmax:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbc:βQ≤εBal/4:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbd:βQ≤εRef/4:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  exact ⟨εQ,βQ,he,(by linarith),(by linarith),hb,(by linarith),hba,hbb,hbc,hbd⟩
end Oberwolfach
