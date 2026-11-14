module

public import Oberwolfach.OrdinaryFineCoverRateCapChoice

@[expose] public section
/-! A root fixed before the matching tolerances remains admissible provided
its explicit size is below the later matching-load threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fine_cover_late_pairing_rate_choice
    (m:ℕ) (target lam:ℝ) (htarget:0<target) (hlam:0≤lam) (hlam1:lam≤1)
    (hlamTarget:lam≤target/(100*((m:ℝ)+2))):
    ∃loadCap:ℝ,0<loadCap ∧ ∀load ξ:ℝ,0≤load→load≤loadCap→load≤1→0≤ξ→ξ≤load^2/160→
      max (18*load+3*lam) ((3*load+lam)*((m:ℝ)+1))≤target ∧ 10*ξ≤target:=by
  let M:ℝ:=(m:ℝ)+2
  have hM:0<M:=by dsimp [M];positivity
  let z:ℝ:=min 1 (target/(100*M))
  have hz:0<z:=by dsimp [z];positivity
  have hlamz:lam≤z:=le_min hlam1 hlamTarget
  have hzt:z≤target/(100*M):=min_le_right _ _
  have hmul:z*(100*M)≤target:=(le_div_iff₀ (by positivity:0<100*M)).mp hzt
  refine ⟨z,hz,?_⟩
  intro load ξ hload hloadz hload1 hξ hξcap
  have hm0:0≤(m:ℝ):=Nat.cast_nonneg _
  have hzm:0≤z*(m:ℝ):=mul_nonneg hz.le hm0
  have hsq:load^2≤load:=by nlinarith [mul_nonneg hload (sub_nonneg.mpr hload1)]
  constructor
  · apply max_le
    · dsimp [M] at hmul
      nlinarith only [hmul,hlamz,hloadz,hz.le,hzm]
    · dsimp [M] at hmul
      have hmload:=mul_le_mul_of_nonneg_right hloadz (show 0≤(m:ℝ)+1 by positivity)
      have hmlam:=mul_le_mul_of_nonneg_right hlamz (show 0≤(m:ℝ)+1 by positivity)
      nlinarith only [hmul,hmload,hmlam,hz.le,hzm]
  · dsimp [M] at hmul
    nlinarith only [hξcap,hsq,hloadz,hmul,hz.le,hzm]

theorem ordinary_two_step_late_pairing_size_obstruction
    (ε lam κ ζ:ℝ) (hε:0<ε) (hε1:ε≤1) (hlam:2*ε^2≤lam)
    (hκ:0≤κ) (hκsmall:κ≤ε) (hζ:0≤ζ) (hζsmall:ζ≤ε)
    (hroot:lam≤ζ*κ/64):False:=by
  have hprod:ζ*κ≤ε^2:=by
    have hh:=mul_le_mul hζsmall hκsmall hκ hε.le
    nlinarith only [hh]
  have hs:0<ε^2:=sq_pos_of_pos hε
  nlinarith only [hprod,hlam,hroot,hs]
end Oberwolfach
