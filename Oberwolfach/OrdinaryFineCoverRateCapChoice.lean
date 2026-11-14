module

public import Oberwolfach.OrdinaryFineCoverNormalizedRates

@[expose] public section
/-! The root and load caps can be chosen in advance so both normalized
fine-cover rates fit any requested positive completion allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fine_cover_rate_cap_choice (m:ℕ) (target:ℝ) (htarget:0<target):
    ∃rootCap loadCap:ℝ,0<rootCap ∧ 0<loadCap ∧
    ∀lam κ ξ:ℝ,0≤lam→lam≤rootCap→0≤κ→κ≤loadCap→κ≤1→0≤ξ→ξ≤κ^2/160→
      max (18*κ+3*lam) ((3*κ+lam)*((m:ℝ)+1))≤target ∧ 10*ξ≤target:=by
  let M:ℝ:=(m:ℝ)+2
  have hM:0<M:=by dsimp [M];positivity
  let z:ℝ:=min 1 (target/(100*M))
  have hz:0<z:=by dsimp [z];positivity
  have hzt:z≤target/(100*M):=min_le_right _ _
  have hmul:z*(100*M)≤target:=(le_div_iff₀ (by positivity:0<100*M)).mp hzt
  refine ⟨z,z,hz,hz,?_⟩
  intro lam κ ξ hlam hlamz hκ hκz hκ1 hξ hξcap
  have hm0:0≤(m:ℝ):=Nat.cast_nonneg _
  have hzm:0≤z*(m:ℝ):=mul_nonneg hz.le hm0
  have hsq:κ^2≤κ:=by nlinarith [mul_nonneg hκ (sub_nonneg.mpr hκ1)]
  constructor
  · apply max_le
    · dsimp [M] at hmul
      nlinarith only [hmul,hlamz,hκz,hz.le,hzm]
    · dsimp [M] at hmul
      have hκm:=mul_le_mul_of_nonneg_right hκz (show 0≤(m:ℝ)+1 by positivity)
      have hlamm:=mul_le_mul_of_nonneg_right hlamz (show 0≤(m:ℝ)+1 by positivity)
      nlinarith only [hmul,hκm,hlamm,hz.le,hzm]
  · dsimp [M] at hmul
    nlinarith only [hξcap,hsq,hκz,hmul,hz.le,hzm]
end Oberwolfach
