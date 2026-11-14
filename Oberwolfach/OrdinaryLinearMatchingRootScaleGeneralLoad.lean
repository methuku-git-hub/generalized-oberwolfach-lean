module

public import Oberwolfach.OrdinaryLinearMatchingRootScaleChoice

@[expose] public section
/-! A fixed deep-cover load multiplier can be absorbed by shrinking the
quadratic vortex scale before any sampling parameter is selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_linear_matching_root_scale_general_load
    (m loadK:ℕ) (root edit eCoeff hCoeff εcap c:ℝ)
    (hroot:0<root) (hedit:0<edit) (he:0<eCoeff) (hh:0<hCoeff) (hεcap:0<εcap) (hc:0<c):
    ∃ε lam βe βh θmatch:ℝ,0<ε ∧ ε ≤ εcap ∧ ε<1/4 ∧ lam=2*ε^2 ∧ 0<lam ∧ lam ≤ root ∧ lam ≤ 1/4 ∧
      βe=eCoeff*ε ∧ βh=hCoeff*ε ∧ 0<βe ∧ 0<βh ∧
      lam ≤ βe/4 ∧ lam ≤ βh/2 ∧ 3*(((loadK:ℝ)+1)*lam) ≤ edit/4 ∧ lam*((m:ℝ)+1) ≤ edit/4 ∧
      θmatch=c*ε ∧ 0<θmatch ∧ ((loadK:ℝ)+1)*lam ≤ 1 ∧
      100*((m:ℝ)+2)*(((loadK:ℝ)+1)*lam) ≤ θmatch/64 :=by
  let K:ℝ:=(loadK:ℝ)+1
  have hK:0<K:=by dsimp [K];positivity
  have hK1:1 ≤ K:=by
    have hk0:(0:ℝ) ≤ loadK:=by positivity
    dsimp [K];linarith
  let root':=min root (1/K)
  let edit':=edit/K
  let c':=c/K
  have hroot':0<root':=by dsimp [root'];positivity
  have hedit':0<edit':=by dsimp [edit'];positivity
  have hc':0<c':=by dsimp [c'];positivity
  obtain ⟨ε,lam,βe,βh,θ',hε,hεcap',hε1,hlameq,hlam,hlamroot,hlam1,hβeeq,hβheq,hβe,hβh,
    hlame,hlamh,hrow,hlevel,hθeq,hθ,hbudget⟩:=
    ordinary_linear_matching_root_scale_choice m root' edit' eCoeff hCoeff εcap c' hroot' hedit' he hh hεcap hc'
  have hlamroot':lam ≤ root:=hlamroot.trans (min_le_left _ _)
  have hwide:K*lam ≤ 1:=by
    have hh':=hlamroot.trans (min_le_right root (1/K))
    have hh2:lam*K ≤ 1:=(le_div_iff₀ hK).mp hh'
    nlinarith only [hh2]
  have hrow':3*(K*lam) ≤ edit/4:=by
    have ht:=mul_le_mul_of_nonneg_left hrow hK.le
    have heq:K*edit'=edit:=by dsimp [edit'];field_simp
    nlinarith only [ht,heq]
  have hlevel':lam*((m:ℝ)+1) ≤ edit/4:=by
    have he':edit' ≤ edit:=by
      dsimp [edit']
      apply (div_le_self hedit.le hK1)
    linarith
  have hθwide:K*θ'=c*ε:=by
    rw [hθeq]
    dsimp [c']
    field_simp
  have hbudget':100*((m:ℝ)+2)*(K*lam) ≤ (c*ε)/64:=by
    have ht:=mul_le_mul_of_nonneg_left hbudget hK.le
    nlinarith only [ht,hθwide]
  refine ⟨ε,lam,βe,βh,c*ε,hε,hεcap',hε1,hlameq,hlam,hlamroot',hlam1,hβeeq,hβheq,hβe,hβh,
    hlame,hlamh,?_,hlevel',rfl,mul_pos hc hε,?_,?_⟩
  · simpa only [K] using hrow'
  · simpa only [K] using hwide
  · simpa only [K] using hbudget'
end Oberwolfach
