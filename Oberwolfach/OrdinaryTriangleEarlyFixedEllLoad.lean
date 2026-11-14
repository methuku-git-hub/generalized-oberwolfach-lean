module

public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy

@[expose] public section
/-! A protected root chosen before sampling leaves a positive fine-cover
load allowance below the fixed outer budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_early_fixed_ell_load
    (lam ellCap othercap:ℝ) (hlam:0≤lam) (hell:0<ellCap) (hother:0<othercap)
    (hroot:400*lam≤ellCap):
    ∃loadCap:ℝ,0<loadCap ∧ loadCap≤1 ∧ loadCap≤othercap ∧
      ∀aLoad:ℝ,0≤aLoad→aLoad≤loadCap→
        max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap :=by
  let loadCap:=min (1/2:ℝ) (min othercap (ellCap/100))
  have hp:0<loadCap:=by dsimp [loadCap];positivity
  have h1:loadCap≤1:=by have hh:=min_le_left (1/2:ℝ) (min othercap (ellCap/100));dsimp [loadCap];linarith
  have ho:loadCap≤othercap:=(min_le_right _ _).trans (min_le_left _ _)
  have hbound:loadCap≤ellCap/100:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨loadCap,hp,h1,ho,?_⟩
  intro aLoad ha hacap
  have ha':aLoad≤ellCap/100:=hacap.trans hbound
  apply max_le <;> nlinarith
end Oberwolfach
