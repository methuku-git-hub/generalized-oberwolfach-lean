module

public import Oberwolfach.OrdinaryFineCoverRateCapChoice

@[expose] public section
/-! A quadratic root scale leaves a positive fine-cover load allowance
under a matching budget proportional to the vortex scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_linear_matching_fine_cover_cap
    (m:ℕ) (lam θmatch:ℝ) (hlam:0≤lam) (hlam1:lam≤1) (hθ:0<θmatch)
    (hroot:100*((m:ℝ)+2)*lam≤θmatch/64):
    ∃loadCap:ℝ,0<loadCap ∧ loadCap≤1 ∧
      ∀load ξ:ℝ,0≤load→load≤loadCap→0≤ξ→ξ≤load^2/160→
        max (18*load+3*lam) ((3*load+lam)*((m:ℝ)+1))≤θmatch/64 ∧ 10*ξ≤θmatch/64:=by
  let M:ℝ:=(m:ℝ)+2
  have hM:0<M:=by dsimp [M];positivity
  let z:ℝ:=min 1 (θmatch/(6400*M))
  have hz:0<z:=by dsimp [z];positivity
  have hz1:z≤1:=min_le_left _ _
  have hzt:z≤θmatch/(6400*M):=min_le_right _ _
  have hmul:z*(100*M)≤θmatch/64:=by
    have hh:=(le_div_iff₀ (by positivity:0<6400*M)).mp hzt
    nlinarith only [hh]
  have hlamz:lam≤z:=by
    apply le_min hlam1
    apply (le_div_iff₀ (by positivity:0<6400*M)).mpr
    dsimp [M] at hroot ⊢
    nlinarith only [hroot]
  refine ⟨z,hz,hz1,?_⟩
  intro load ξ hload hloadz hξ hξcap
  have hload1:load≤1:=hloadz.trans hz1
  have hm0:0≤(m:ℝ):=Nat.cast_nonneg _
  have hzm:0≤z*(m:ℝ):=mul_nonneg hz.le hm0
  have hsq:load^2≤load:=by nlinarith [mul_nonneg hload (sub_nonneg.mpr hload1)]
  constructor
  · apply max_le
    · dsimp [M] at hmul
      nlinarith only [hmul,hlamz,hloadz,hz.le,hzm]
    · dsimp [M] at hmul
      have hlm:=mul_le_mul_of_nonneg_right hlamz (show 0≤(m:ℝ)+1 by positivity)
      have hkm:=mul_le_mul_of_nonneg_right hloadz (show 0≤(m:ℝ)+1 by positivity)
      nlinarith only [hmul,hlm,hkm,hz.le,hzm]
  · dsimp [M] at hmul
    nlinarith only [hξcap,hsq,hloadz,hmul,hz.le,hzm]
end Oberwolfach
