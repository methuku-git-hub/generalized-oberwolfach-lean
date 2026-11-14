module

public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

/-- Fix the correction scales before the later deletion, embedding and inner
set, each of which may then be chosen below the returned cap. -/
theorem long_type_correction_scale_choice (c:ℝ) (hc:0<c):
    ∃rho eta cap:ℝ,0<rho ∧ 0<eta ∧ eta≤rho ∧ 0<cap ∧
      ∀ζ δLoss εInner:ℝ,ζ≤cap→δLoss≤cap→εInner≤cap→
        ζ+δLoss<eta ∧ rho+ζ+δLoss+εInner<c:=by
  refine ⟨c/8,c/16,c/64,by positivity,by positivity,by linarith,by positivity,?_⟩
  intro ζ δLoss εInner hζ hδ hε
  constructor <;> linarith
end Oberwolfach
