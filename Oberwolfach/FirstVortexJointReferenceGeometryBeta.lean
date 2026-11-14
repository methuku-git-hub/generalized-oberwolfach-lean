module

public import Mathlib.Tactic

@[expose] public section
/-! One vortex parameter satisfies the parent-event and geometric-record
requirements simultaneously, after their positive caps have been fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_joint_reference_geometry_beta
    (α κ x βmax εBal εRef:ℝ)
    (hα:0<α) (hκ:0<κ) (hx:0<x) (hβ:0<βmax)
    (hBal:0<εBal) (hRef:0<εRef):
    ∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤3*α/40 ∧ β≤3/20 ∧
      β≤κ ∧ β≤x ∧ β≤βmax ∧ β≤εBal/4 ∧ β≤εRef/4 :=by
  let b:ℝ:=min (1:ℝ) (min α (min κ (min x (min βmax (min εBal εRef)))))
  have hb:0<b:=by dsimp [b];positivity
  have h1:b≤1:=min_le_left _ _
  have ha:b≤α:=(min_le_right _ _).trans (min_le_left _ _)
  have hk:b≤κ:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hx':b≤x:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbmax:b≤βmax:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hbal:b≤εBal:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have href:b≤εRef:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  refine ⟨b/100,by positivity,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith
end Oberwolfach
