module

public import Oberwolfach.OrdinaryLinearMatchingRootScaleGeneralLoad

@[expose] public section
/-! Fix the triangle vortex contraction and protected root size before the
retention rate and before the later conflict size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_early_vortex_root_choices
    (ρ₀ root ξreserve edit eCoeff hCoeff εcap cMatch:ℝ)
    (hρ:0<ρ₀) (hroot:0<root) (hξ:0<ξreserve) (hedit:0<edit)
    (he:0<eCoeff) (hh:0<hCoeff) (hεcap:0<εcap) (hc:0<cMatch):
    ∃lam ε βe βh θmatch:ℝ,
      0<ε ∧ ε≤εcap ∧ ε<1/4 ∧ ε≤ξreserve/2 ∧ ε≤ξreserve*(ρ₀/8)/2 ∧
      lam=2*ε^2 ∧ 0<lam ∧ lam≤root ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧
      βe=eCoeff*ε ∧ βh=hCoeff*ε ∧ 0<βe ∧ 0<βh ∧ lam≤βe/4 ∧ lam≤βh/2 ∧
      3*lam≤edit/4 ∧ lam*3≤edit/4 ∧ θmatch=cMatch*ε ∧ 0<θmatch ∧ 400*lam≤θmatch/64 :=by
  let root':=min root ((ρ₀/8)/2)
  let εcap':=min εcap (min (ξreserve/2) (ξreserve*(ρ₀/8)/2))
  have hr:0<root':=by dsimp [root'];positivity
  have hecap:0<εcap':=by dsimp [εcap'];positivity
  obtain ⟨ε,lam,βe,βh,θmatch,hε,hεcap',hε1,hlamEq,hlam,hlamroot,hlam1,hβeeq,hβheq,hβe,hβh,
    hlame,hlamh,hrow,hlevel,hθeq,hθ,_hwide,_hrootScale⟩:=
      ordinary_linear_matching_root_scale_general_load 2 0 root' edit eCoeff hCoeff εcap' cMatch hr hedit he hh hecap hc
  refine ⟨lam,ε,βe,βh,θmatch,hε,hεcap'.trans (min_le_left _ _),hε1,
    hεcap'.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hεcap'.trans ((min_le_right _ _).trans (min_le_right _ _)),hlamEq,hlam,
    hlamroot.trans (min_le_left _ _),hlam1,hlamroot.trans (min_le_right _ _),
    hβeeq,hβheq,hβe,hβh,hlame,hlamh,?_,?_,hθeq,hθ,?_⟩
  · simpa using hrow
  · nlinarith only [hlevel]
  · nlinarith only [_hrootScale]
end Oberwolfach
