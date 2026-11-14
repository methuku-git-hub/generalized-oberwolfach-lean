module

public import Mathlib.Tactic

@[expose] public section
/-! Concrete density lower bounds shared by the parent selector, the
matching event and the uniform level-step theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_seed_density_alignment
    (r:ℕ) (ρ₀ ρ t:ℝ) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1)
    (ht:1/(200*((r+4:ℕ):ℝ))≤t):
    let m:ℝ:=(r+4:ℕ)
    let sstar:ℝ:=1/100
    let tstar:ℝ:=1/(200*m)
    let kstar:ℝ:=ρ₀/(800*m)
    let p:ℝ:=ρ*sstar/2
    let kval:ℝ:=p/m;
    0<sstar ∧ sstar≤1/100 ∧ 0<tstar ∧ tstar≤1 ∧ tstar≤sstar ∧ tstar≤(1/100)/m ∧
    0<kstar ∧ kstar≤ρ*sstar/2 ∧ kstar≤ρ*((1/100)/m)/2 ∧
    4*m*kstar≤ρ₀*(1/100) ∧ kstar≤p ∧ kstar≤kval ∧ kstar≤sstar ∧
    p≤1 ∧ kval≤1 ∧ sstar≤1 ∧
    ρ₀/400≤ρ*m*t/2 ∧ kstar≤ρ*m*t/2 ∧ kstar≤ρ*t/2 ∧ kstar≤t :=by
  intro m sstar tstar kstar p kval
  have hm:0<m:=by dsimp [m];positivity
  have hm4:4≤m:=by
    dsimp [m]
    have hr:0≤(r:ℝ):=by positivity
    push_cast
    linarith
  have hρ:0<ρ:=hρ₀.trans_le hρlo
  have hρ₀one:ρ₀≤1:=hρlo.trans hρhi
  have htstar:0<tstar:=by dsimp [tstar];positivity
  have ht':tstar≤t:=by simpa only [tstar,m] using ht
  have hk:0<kstar:=by dsimp [kstar];positivity
  have htm:m*tstar=1/200:=by dsimp [tstar];field_simp
  have hks:kstar=ρ₀*tstar/4:=by dsimp [kstar,tstar];field_simp;ring
  have hts:tstar≤1/200:=by
    dsimp [tstar]
    apply (div_le_iff₀ (show 0<200*m by positivity)).2
    nlinarith
  have htcap:tstar≤(1/100:ℝ)/m:=by
    dsimp [tstar]
    apply (div_le_iff₀ (show 0<200*m by positivity)).2
    have heq:(1/100:ℝ)/m*(200*m)=2:=by field_simp;norm_num
    rw [heq]
    norm_num
  have hkm:kstar≤ρ/(200*m):=by
    dsimp [kstar]
    apply (div_le_iff₀ (show 0<800*m by positivity)).2
    have heq:(ρ/(200*m))*(800*m)=4*ρ:=by field_simp;ring
    rw [heq]
    linarith
  have hkval:kstar≤kval:=by
    have heq:kval=ρ/(200*m):=by dsimp [kval,p,sstar];field_simp;ring
    rw [heq]
    exact hkm
  have hkp:kstar≤p:=by
    have hh:ρ/(200*m)≤ρ/200:=by
      apply (div_le_iff₀ (show 0<200*m by positivity)).2
      nlinarith [mul_nonneg hρ.le (show 0≤m-1 by linarith)]
    have hp:p=ρ/200:=by dsimp [p,sstar];ring
    rw [hp]
    exact hkm.trans hh
  have hksstar:kstar≤sstar:=by
    have hp:p≤sstar:=by dsimp [p,sstar];linarith
    exact hkp.trans hp
  have hp1:p≤1:=by dsimp [p,sstar];linarith
  have hk1:kval≤1:=by
    have heq:kval=ρ/(200*m):=by dsimp [kval,p,sstar];field_simp;ring
    rw [heq]
    apply (div_le_iff₀ (show 0<200*m by positivity)).2
    nlinarith
  have hq:4*m*kstar≤ρ₀*(1/100:ℝ):=by
    have heq:4*m*kstar=ρ₀/200:=by dsimp [kstar];field_simp;ring
    rw [heq]
    linarith
  have hmul:ρ₀*tstar≤ρ*t:=by
    have h1:=mul_le_mul_of_nonneg_right hρlo htstar.le
    have h2:=mul_le_mul_of_nonneg_left ht' hρ.le
    linarith
  have hmprod:ρ₀/400≤ρ*m*t/2:=by
    have hh:=mul_le_mul_of_nonneg_left hmul hm.le
    nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hρlo)]
  have hkt:kstar≤ρ*t/2:=by rw [hks];nlinarith
  have hkmt:kstar≤ρ*m*t/2:=by
    have hh:=mul_le_mul_of_nonneg_left (show (1:ℝ)≤m by linarith) (mul_nonneg hρ.le (le_trans htstar.le ht'))
    nlinarith
  have hkt':kstar≤t:=by rw [hks];nlinarith [mul_nonneg htstar.le (sub_nonneg.mpr hρ₀one)]
  refine ⟨by dsimp [sstar];norm_num,by dsimp [sstar];norm_num,htstar,by linarith,by dsimp [sstar];linarith,htcap,
    hk,?_,?_,hq,hkp,hkval,hksstar,hp1,hk1,by dsimp [sstar];norm_num,hmprod,hkmt,hkt,hkt'⟩
  · simpa only [p] using hkp
  · have heq:ρ*((1/100:ℝ)/m)/2=kval:=by dsimp [kval,p,sstar];ring
    rw [heq]
    exact hkval
end Oberwolfach
