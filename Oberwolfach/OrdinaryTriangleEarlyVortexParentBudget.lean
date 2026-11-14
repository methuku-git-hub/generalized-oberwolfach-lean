module

public import Oberwolfach.OrdinaryTriangleEarlyVortexRootChoices
public import Oberwolfach.OrdinaryTriangleEarlyParentBudgetCoefficients

@[expose] public section
/-! One early choice of vortex contraction and root scale fits the parent
budgets and leaves a fixed outer allowance for the later sampling rate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_early_vortex_parent_budget
    (ρ₀ root ξreserve edit εcap eParent hParent ζfresh γbase:ℝ)
    (hρ:0<ρ₀) (hroot:0<root) (hξ:0<ξreserve) (hedit:0<edit) (hεcap:0<εcap)
    (he:0<eParent) (hh:0<hParent) (hζ:0<ζfresh) (hγ:0<γbase):
    ∃lam ε βe βh θmatch ellCap:ℝ,
      0<ε ∧ ε≤εcap ∧ ε<1/4 ∧ ε≤ξreserve/2 ∧ ε≤ξreserve*(ρ₀/8)/2 ∧
      lam=2*ε^2 ∧ 0<lam ∧ lam≤root ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧
      0<βe ∧ 0<βh ∧ lam≤βe/4 ∧ lam≤βh/2 ∧
      3*lam≤edit/4 ∧ lam*3≤edit/4 ∧ 0<θmatch ∧
      ellCap=θmatch/64 ∧ 0<ellCap ∧ 400*lam≤ellCap ∧
      ellCap≤ζfresh*(γbase*ε)/8 ∧
      (∀ηCap:ℝ,0≤ηCap→ηCap≤ellCap→
        βe+3*max ηCap ellCap≤eParent*ε ∧ βh+2*ellCap≤hParent*ε) :=by
  obtain ⟨eCoeff,hCoeff,cMatch,hec,hhc,hc,hecCap,hhcCap,hmatch,hbudgets⟩:=
    ordinary_triangle_early_parent_budget_coefficients eParent hParent ζfresh γbase he hh hζ hγ
  obtain ⟨lam,ε,βe,βh,θmatch,hε,hεcap',hε1,hεξ,hερ,hlameq,hlam,hlamroot,hlam1,hlamρ,
    hβeeq,hβheq,hβe,hβh,hlamE,hlamH,hrow,hlevel,hθeq,hθ,hwide⟩:=
      ordinary_triangle_early_vortex_root_choices ρ₀ root ξreserve edit eCoeff hCoeff εcap cMatch
        hρ hroot hξ hedit hec hhc hεcap hc
  let ellCap:=θmatch/64
  have heq:ellCap=cMatch*ε/64:=by dsimp [ellCap];rw [hθeq]
  obtain ⟨hell,hellscale,hbudget⟩:=hbudgets ε hε
  refine ⟨lam,ε,βe,βh,θmatch,ellCap,hε,hεcap',hε1,hεξ,hερ,hlameq,hlam,hlamroot,hlam1,hlamρ,
    hβe,hβh,hlamE,hlamH,hrow,hlevel,hθ,rfl,?_,?_,?_,?_⟩
  · simpa only [heq] using hell
  · exact hwide
  · simpa only [heq] using hellscale
  · intro ηCap hη hηcap
    have hb:=hbudget ηCap hη (by simpa only [heq] using hηcap)
    simpa only [hβeeq,hβheq,heq] using hb
end Oberwolfach
