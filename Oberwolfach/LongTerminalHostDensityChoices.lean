module

public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_terminal_host_density_choices
    (r:ℕ) (ρ₀:ℝ) (hρ₀:0<ρ₀) (hρ₀1:ρ₀≤1):
    let m:ℝ:=((r+4:ℕ):ℝ)
    let sstar:ℝ:=1/100
    let tstar:ℝ:=sstar/m
    let kstar:ℝ:=ρ₀*tstar/4
    let pA0:ℝ:=ρ₀/400
    let ω:ℝ:=ρ₀/16
    0<m ∧ 1≤m ∧ 0<sstar ∧ sstar≤1/100 ∧ 0<tstar ∧ tstar≤1 ∧ tstar≤sstar ∧
    0<kstar ∧ 0<pA0 ∧ pA0≤1/2 ∧ 0<ω ∧ 4*ω≤ρ₀ ∧
    tstar=(1/100)/m ∧ ρ₀*sstar/(2*m)=ρ₀*tstar/2 ∧
    ∀ rho t:ℝ,ρ₀ ≤ rho → rho≤1 → tstar ≤ t →
      pA0≤ rho*m*t/2 ∧ kstar≤ rho*m*t/2 ∧ kstar≤ rho*t/2 ∧ kstar ≤ t :=by
  intro m sstar tstar kstar pA0 ω
  have hm:0<m:=by dsimp [m];positivity
  have hm1:1≤m:=by dsimp [m];norm_num; exact_mod_cast (show 1≤r+4 by omega)
  have ht:0<tstar:=by dsimp [tstar,sstar];positivity
  have htm:m*tstar=sstar:=by dsimp [tstar];field_simp
  have htS:tstar≤sstar:=by
    dsimp [tstar]
    apply (div_le_iff₀ hm).2
    dsimp [sstar]
    nlinarith
  refine ⟨hm,hm1,by dsimp [sstar];norm_num,by dsimp [sstar];norm_num,ht,by dsimp [sstar] at htS;linarith,
    htS,by dsimp [kstar];positivity,by dsimp [pA0];positivity,?_,by dsimp [ω];positivity,?_,rfl,?_,?_⟩
  · dsimp [pA0];linarith
  · dsimp [ω];linarith
  · dsimp [tstar];ring
  intro rho t hrho hrho1 htlo
  have hrhop:0<rho:=hρ₀.trans_le hrho
  have htpos:0<t:=ht.trans_le htlo
  have hprod:ρ₀*tstar≤ rho*t:=mul_le_mul hrho htlo ht.le hrhop.le
  have hprodm:ρ₀*sstar≤ rho*m*t:=by
    have hh:=mul_le_mul_of_nonneg_left hprod hm.le
    rw [show m*(ρ₀*tstar)=ρ₀*(m*tstar) by ring,htm] at hh
    nlinarith
  have hk1:kstar≤ rho*t/2:=by dsimp [kstar];nlinarith
  have hmt:rho*t≤ rho*m*t:=by nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (mul_nonneg hrhop.le htpos.le)]
  refine ⟨?_,?_,hk1,?_⟩
  · dsimp [pA0,sstar] at *;nlinarith
  · dsimp [kstar,sstar] at *;nlinarith
  · dsimp [kstar] at *;nlinarith [mul_nonneg (sub_nonneg.mpr hρ₀1) ht.le]
end Oberwolfach
