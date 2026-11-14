module

public import Mathlib.Tactic

@[expose] public section
/-! Select the triangle concentration tolerance and the vortex degree error
strictly positively from the original positive margin and density scales. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_nondeeper_triangle_tolerance_choice
    (α pstar ω:ℝ) (hα:0<α) (hp:0<pstar) (hω:0<ω):
    ∃βP:ℝ,0<βP ∧ βP≤2*(min (α/2) (1/4))*pstar^4*pstar^4 ∧ βP≤ω*pstar^9/4 ∧
      ∀εTri:ℝ,0<εTri→∃βmax:ℝ,0<βmax ∧ βmax≤1/4 ∧ βmax≤3*(2*α)/20 ∧ (5/3)*βmax≤εTri :=by
  let A:=2*(min (α/2) (1/4))*pstar^4*pstar^4
  let B:=ω*pstar^9/4
  have hA:0<A:=by dsimp [A];positivity
  have hB:0<B:=by dsimp [B];positivity
  refine ⟨min A B/2,by positivity,?_,?_,?_⟩
  · have hh:=min_le_left A B
    dsimp [A] at *
    linarith
  · have hh:=min_le_right A B
    dsimp [B] at *
    linarith
  · intro εTri hε
    let C:=min (1/4:ℝ) (min (3*(2*α)/20) (3*εTri/5))
    have hC:0<C:=by dsimp [C];positivity
    refine ⟨C/2,by positivity,?_,?_,?_⟩
    · have hh:=min_le_left (1/4:ℝ) (min (3*(2*α)/20) (3*εTri/5))
      dsimp [C]
      linarith
    · have hh: C≤3*(2*α)/20:=le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    · have hh: C≤3*εTri/5:=le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
end Oberwolfach
