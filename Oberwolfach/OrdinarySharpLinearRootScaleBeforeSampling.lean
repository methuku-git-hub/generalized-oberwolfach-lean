module

public import Oberwolfach.OrdinarySharpBufferedRootScaleChoiceBeforeSampling

@[expose] public section
/-! Select the vortex first, then root and extension rates linear in that
vortex scale. The hub-size condition is independent of the later sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_sharp_linear_root_scale_before_sampling
    (m:ℕ) (root edit eCoeff hCoeff cap:ℝ)
    (hroot:0<root) (hedit:0<edit) (he:0<eCoeff) (hh:0<hCoeff) (hcap:0<cap):
    ∃ε lam βe βh:ℝ,0<ε ∧ ε≤cap ∧ ε<1/4 ∧
      lam=2*ε^2 ∧ 0<lam ∧ lam≤root ∧ lam≤1/4 ∧
      βe=eCoeff*ε ∧ βh=hCoeff*ε ∧ 0<βe ∧ 0<βh ∧
      lam≤βe/4 ∧ lam≤βh/2 ∧ 3*lam≤edit/4 ∧ lam*((m:ℝ)+1)≤edit/4:=by
  let M:ℝ:=(m:ℝ)+2
  have hM:0<M:=by dsimp [M];positivity
  let ε:ℝ:=min (1/16:ℝ) (min (cap/2) (min (root/4)
    (min (eCoeff/16) (min (hCoeff/8) (edit/(48*M))))))
  have hε:0<ε:=by dsimp [ε];positivity
  have hεone:ε≤1/16:=min_le_left _ _
  have hεcap:ε≤cap/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hεroot:ε≤root/4:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεe:ε≤eCoeff/16:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεh:ε≤hCoeff/8:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεedit:ε≤edit/(48*M):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hsq:ε^2≤ε:=by nlinarith [mul_nonneg hε.le (by linarith:0≤1-ε)]
  have heditmul:ε*(48*M)≤edit:=(le_div_iff₀ (by positivity:0<48*M)).mp hεedit
  have hm:0≤(m:ℝ):=Nat.cast_nonneg _
  have hmul:0≤ε*(m:ℝ):=mul_nonneg hε.le hm
  have hE:=mul_le_mul_of_nonneg_right hεe hε.le
  have hH:=mul_le_mul_of_nonneg_right hεh hε.le
  refine ⟨ε,2*ε^2,eCoeff*ε,hCoeff*ε,hε,by linarith,by linarith,rfl,by positivity,?_,?_,rfl,rfl,by positivity,by positivity,?_,?_,?_,?_⟩
  · nlinarith [hsq,hεroot]
  · nlinarith [hsq,hεone]
  · nlinarith only [hE]
  · nlinarith only [hH]
  · dsimp [M] at heditmul; nlinarith only [heditmul,hsq,hmul,hε.le]
  · dsimp [M] at heditmul; nlinarith only [heditmul,hsq,hmul,hε.le]
end Oberwolfach
