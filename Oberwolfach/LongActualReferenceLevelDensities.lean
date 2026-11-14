module

public import Oberwolfach.MarkedCoupledReferenceDensityBounds

@[expose] public section
/-! The long matching's fixed selected density supplies the level theorem's
coupled density bounds with the same index-density lower bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_actual_reference_level_densities
    (m:ℕ) (hm:1≤m) (ρ₀ ρ tstar kstar:ℝ)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1)
    (ht:0<tstar) (htcap:tstar≤(1/100)/(m:ℝ))
    (hk:0<kstar) (hkcap:kstar≤ρ*((1/100)/(m:ℝ))/2):
    let omega₀:=ρ₀/8
    let pA0:=ρ₀/400
    let t:ℝ:=(1/100)/(m:ℝ);
    ρ₀≤1 ∧ 0<omega₀ ∧ omega₀≤1 ∧ 0<tstar ∧ tstar≤1 ∧
    0<pA0 ∧ pA0≤1/2 ∧ 0<kstar ∧ kstar≤1/2 ∧
    tstar≤t ∧ (m:ℝ)*t≤1 ∧ pA0≤ρ*(m:ℝ)*t/2 ∧
    kstar≤ρ*(m:ℝ)*t/2 ∧ kstar≤ρ*t/2 ∧ kstar≤t := by
  intro omega₀ pA0 t
  have hm1:(1:ℝ)≤m:=by exact_mod_cast hm
  have hmpos:0<(m:ℝ):=by positivity
  have hρ:0<ρ:=hρ₀.trans_le hρlo
  have hρ₀1:ρ₀≤1:=hρlo.trans hρhi
  have htpos:0<t:=by dsimp [t];positivity
  have htid:(m:ℝ)*t=(1/100:ℝ):=by dsimp [t];field_simp
  have htupper:t≤1/100:=by
    dsimp [t]
    apply (div_le_iff₀ hmpos).2
    nlinarith
  have htstar1:tstar≤1:=by linarith
  have hω:0<omega₀:=by dsimp [omega₀];positivity
  have hω1:omega₀≤1:=by dsimp [omega₀];linarith
  have hp:0<pA0:=by dsimp [pA0];positivity
  have hp1:pA0≤1/2:=by dsimp [pA0];linarith
  have hkhalf:kstar≤ρ*t/2:=by simpa only [t] using hkcap
  have hkt:kstar≤t:=by
    have hh:=mul_le_mul_of_nonneg_right hρhi htpos.le
    nlinarith
  have hk1:kstar≤1/2:=by linarith
  have hpbound:pA0≤ρ*(m:ℝ)*t/2:=by
    rw [mul_assoc,htid]
    dsimp [pA0]
    linarith
  have hkm:kstar≤ρ*(m:ℝ)*t/2:=by
    have hh:=mul_nonneg (sub_nonneg.mpr hm1) (mul_nonneg hρ.le htpos.le)
    nlinarith
  exact ⟨hρ₀1,hω,hω1,ht,htstar1,hp,hp1,hk,hk1,htcap,by rw [htid];norm_num,
    hpbound,hkm,hkhalf,hkt⟩
end Oberwolfach
