module

public import Oberwolfach.OrdinaryBoundarySelectionMargins

@[expose] public section
/-! The sampling density can be chosen before the graph order so that the
selection margins required at a linear-size class are available. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_boundary_small_density_choice (κ ζ pmax:ℝ) (hκ:0<κ) (hζ:0<ζ) (hpmax:0<pmax):
    ∃p:ℝ,0<p ∧ p≤1 ∧ p≤pmax ∧ p≤4*ζ*κ ∧ 20*Real.sqrt (2*p)≤ζ*κ/2:=by
  let t:=min (1/2:ℝ) (min (ζ*κ/80) (Real.sqrt (2*pmax)))
  have ht:0<t:=lt_min (by norm_num) (lt_min (by positivity) (Real.sqrt_pos.2 (by positivity)))
  have ht1:t≤1/2:=min_le_left _ _
  have htk:t≤ζ*κ/80:=(min_le_right _ _).trans (min_le_left _ _)
  have htp:t≤Real.sqrt (2*pmax):=(min_le_right _ _).trans (min_le_right _ _)
  let p:=t^2/2
  have hp:0<p:=by dsimp [p];positivity
  have htsq:t^2≤t:=by nlinarith only [ht.le,ht1,mul_nonneg ht.le (by linarith:0≤1-t)]
  have htsmall:t≤ζ*κ/80:=htk
  have hmax:t^2≤2*pmax:=by
    have hh:=sq_le_sq₀ ht.le (Real.sqrt_nonneg (2*pmax)) |>.mpr htp
    rw [Real.sq_sqrt (by positivity:0≤2*pmax)] at hh
    exact hh
  have hsqrt:Real.sqrt (2*p)=t:=by
    dsimp [p]
    rw [show 2*(t^2/2)=t^2 by ring,Real.sqrt_sq ht.le]
  refine ⟨p,hp,?_,?_,?_,?_⟩
  · dsimp [p];nlinarith only [htsq,ht1]
  · dsimp [p];linarith
  · dsimp [p];nlinarith only [htsq,htsmall,mul_pos hζ hκ]
  · rw [hsqrt];nlinarith only [htsmall,mul_pos hζ hκ]
end Oberwolfach
