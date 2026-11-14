module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
/-! With boundary-based load control, the dual correction and completion
budgets can be chosen together for every positive original density. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_boundary_dual_budget_choice
    (ρ₀ βfinal:ℝ) (m:ℕ) (hρ₀:0<ρ₀) (hβ:0<βfinal) (hm:0<m):
    ∃rho eta δLoss εInner δglobal ζmax:ℝ,
      0<rho ∧ 0<eta ∧ eta≤rho ∧ 0<δLoss ∧ 0<εInner ∧
      0<δglobal ∧ δglobal≤(βfinal/100)^2 ∧ 5*Real.sqrt δglobal≤δLoss ∧ 0<ζmax ∧
      ∀ζ:ℝ,0≤ζ→ζ≤ζmax→ζ+δLoss<eta ∧
        rho+ζ+δLoss+εInner<ρ₀/(400*(m:ℝ)) :=by
  let x:ℝ:=ρ₀/(4000*(m:ℝ))
  have hmR:0<(m:ℝ):=by exact_mod_cast hm
  have hx:0<x:=by dsimp [x];positivity
  let δLoss:ℝ:=x/4
  let δglobal:ℝ:=min ((βfinal/100)^2) ((δLoss/5)^2)/2
  have hLoss:0<δLoss:=by dsimp [δLoss];positivity
  have hglobal:0<δglobal:=by dsimp [δglobal];positivity
  have hβbound:δglobal≤(βfinal/100)^2:=by
    dsimp [δglobal]
    have hh:=min_le_left ((βfinal/100)^2) ((δLoss/5)^2)
    have hn:0≤(βfinal/100)^2:=sq_nonneg _
    linarith
  have hLossBound:δglobal≤(δLoss/5)^2:=by
    dsimp [δglobal]
    have hh:=min_le_right ((βfinal/100)^2) ((δLoss/5)^2)
    have hn:0≤(δLoss/5)^2:=sq_nonneg _
    linarith
  have hsqrt:Real.sqrt δglobal≤δLoss/5:=Real.sqrt_le_iff.mpr ⟨by positivity,hLossBound⟩
  have hsupply:ρ₀/(400*(m:ℝ))=10*x:=by dsimp [x];ring
  refine ⟨4*x,2*x,δLoss,x,δglobal,x/4,by positivity,by positivity,by linarith,hLoss,hx,hglobal,hβbound,?_,by positivity,?_⟩
  · linarith
  · intro ζ hζ hζmax
    dsimp only [δLoss] at *
    rw [hsupply]
    constructor <;> linarith
end Oberwolfach
