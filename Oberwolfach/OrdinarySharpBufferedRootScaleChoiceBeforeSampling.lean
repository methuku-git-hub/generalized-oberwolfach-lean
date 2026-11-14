module

public import Oberwolfach.OrdinaryRootFreeCleanupCardMargins

@[expose] public section
/-! The buffered root-size coefficient can be fixed before the vortex scale
and independently of the later packing-balance margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sharp_buffered_root_scale_choice_before_sampling
    (m:ℕ) (root edit βe βh:ℝ) (hroot:0<root) (hedit:0<edit)
    (he:0<βe) (hh:0<βh):
    ∃lam:ℝ,0<lam ∧ lam≤root ∧ lam≤1/4 ∧ lam≤βe/4 ∧ lam≤βh/2 ∧
      3*lam≤edit/4 ∧ lam*((m:ℝ)+1)≤edit/4 ∧
    ∀cap:ℝ,0<cap→∃ε:ℝ,0<ε ∧ ε≤cap ∧ ε<1/4 ∧ 2*ε^2≤lam:=by
  let M:ℝ:=(m:ℝ)+2
  have hM:0<M:=by dsimp [M];positivity
  let lam:ℝ:=min (1/8:ℝ) (min (root/2) (min (βe/8) (min (βh/8) (edit/(8*M)))))
  have hlam:0<lam:=by dsimp [lam];positivity
  have h1:lam≤1/8:=min_le_left _ _
  have hroot':lam≤root/2:=(min_le_right _ _).trans (min_le_left _ _)
  have he':lam≤βe/8:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh':lam≤βh/8:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc':lam≤edit/(8*M):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hmul:lam*(8*M)≤edit:=(le_div_iff₀ (by positivity:0<8*M)).mp hc'
  have hm0:0≤(m:ℝ):=Nat.cast_nonneg _
  have hthree:3*lam≤edit/4:=by dsimp [M] at hmul;nlinarith [mul_nonneg hlam.le hm0]
  have hlevel:lam*((m:ℝ)+1)≤edit/4:=by dsimp [M] at hmul;nlinarith [mul_nonneg hlam.le hm0]
  refine ⟨lam,hlam,by linarith,by linarith,by linarith,by linarith,hthree,hlevel,?_⟩
  intro cap hcap
  let ε:ℝ:=min (1/8:ℝ) (min (cap/2) (lam/4))
  have hε:0<ε:=by dsimp [ε];positivity
  have hε1:ε≤1/8:=min_le_left _ _
  have hεcap:ε≤cap/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hεlam:ε≤lam/4:=(min_le_right _ _).trans (min_le_right _ _)
  have hsq:ε^2≤ε:=by nlinarith [mul_nonneg hε.le (by linarith:0≤1-ε)]
  exact ⟨ε,hε,by linarith,by linarith,by nlinarith only [hsq,hεlam,hlam.le]⟩
end Oberwolfach
