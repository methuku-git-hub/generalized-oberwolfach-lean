module

public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy

@[expose] public section
/-! Select coefficients before the vortex contraction so the fixed outer
allowance fits both later parent budgets and the fresh-factor margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_early_parent_budget_coefficients
    (eParent hParent ζfresh γbase:ℝ)
    (he:0<eParent) (hh:0<hParent) (hζ:0<ζfresh) (hγ:0<γbase):
    ∃eCoeff hCoeff cMatch:ℝ,0<eCoeff ∧ 0<hCoeff ∧ 0<cMatch ∧
      eCoeff≤eParent/2 ∧ hCoeff≤hParent/2 ∧ cMatch≤ζfresh*γbase ∧
    ∀ε:ℝ,0<ε→let ellCap:=cMatch*ε/64;
      0<ellCap ∧ ellCap≤ζfresh*(γbase*ε)/8 ∧
      ∀ηCap:ℝ,0≤ηCap→ηCap≤ellCap→
        eCoeff*ε+3*max ηCap ellCap≤eParent*ε ∧
        hCoeff*ε+2*ellCap≤hParent*ε :=by
  let eCoeff:=eParent/4
  let hCoeff:=hParent/4
  let cMatch:=min (ζfresh*γbase) (min eParent hParent)/2
  have hec:0<eCoeff:=by dsimp [eCoeff];positivity
  have hhc:0<hCoeff:=by dsimp [hCoeff];positivity
  have hcm:0<cMatch:=by dsimp [cMatch];positivity
  have hcζ:cMatch≤ζfresh*γbase:=by
    have hm:=min_le_left (ζfresh*γbase) (min eParent hParent)
    dsimp [cMatch];nlinarith [mul_pos hζ hγ]
  have hce:cMatch≤eParent:=by
    have hm: min (ζfresh*γbase) (min eParent hParent)≤eParent:=
      (min_le_right _ _).trans (min_le_left _ _)
    dsimp [cMatch];linarith
  have hch:cMatch≤hParent:=by
    have hm: min (ζfresh*γbase) (min eParent hParent)≤hParent:=
      (min_le_right _ _).trans (min_le_right _ _)
    dsimp [cMatch];linarith
  refine ⟨eCoeff,hCoeff,cMatch,hec,hhc,hcm,by dsimp [eCoeff];linarith,
    by dsimp [hCoeff];linarith,hcζ,?_⟩
  intro ε hε ellCap
  have hE:=mul_le_mul_of_nonneg_right hce hε.le
  have hH:=mul_le_mul_of_nonneg_right hch hε.le
  have hZ:=mul_le_mul_of_nonneg_right hcζ hε.le
  refine ⟨by dsimp [ellCap];positivity,?_,?_⟩
  · dsimp [ellCap];nlinarith [mul_pos hζ (mul_pos hγ hε)]
  · intro ηCap hη hηcap
    rw [max_eq_right hηcap]
    dsimp [ellCap,eCoeff,hCoeff]
    constructor <;> nlinarith
end Oberwolfach
