module

public import Oberwolfach.MarkedSeedDensities

@[expose] public section
/-! The fixed density lower bounds used by the reference step and the
sampled event can be chosen from the same fixed lower data. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_sample_reference_density_hierarchy
    (m:ℕ) (hm:1≤m) (ρ s ρ₀ sstar:ℝ)
    (hρ₀:0<ρ₀) (hsstar:0<sstar) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1)
    (hslo:sstar≤s) (hshi:s≤1/100):
    let t₀:=sstar/m
    let t:=s/m
    let pA0:=ρ₀*sstar/2
    let p0:=ρ₀*sstar/(2*m)
    let p:=ρ*s/2
    let k:=p/m;
    0<ρ₀ ∧ ρ₀≤1 ∧ 0<t₀ ∧ t₀≤1 ∧ t₀≤t ∧ 0<pA0 ∧ pA0≤1/2 ∧
      0<p0 ∧ p0≤1/2 ∧ p0≤p ∧ p0≤k ∧ p0≤t ∧
      pA0≤ρ*m*t/2 ∧ p0≤ρ*m*t/2 ∧ p0≤ρ*t/2 ∧
      p0/2≤ρ₀*t₀/4 ∧ (m:ℝ)*t≤1:=by
  intro t₀ t pA0 p0 p k
  have hmR:0<(m:ℝ):=by exact_mod_cast (show 0<m by omega)
  have hm1:(1:ℝ)≤m:=by exact_mod_cast hm
  have hρ:0<ρ:=hρ₀.trans_le hρlo
  have hs:0<s:=hsstar.trans_le hslo
  have hρ₀1:ρ₀≤1:=hρlo.trans hρhi
  have hsstar1:sstar≤1:=by linarith
  have hs1:s≤1:=by linarith
  have hprod:ρ₀*sstar≤ρ*s:=mul_le_mul hρlo hslo hsstar.le hρ.le
  have ht₀:0<t₀:=by dsimp [t₀];positivity
  have ht₀1:t₀≤1:=by dsimp [t₀];apply (div_le_iff₀ hmR).mpr;linarith
  have htle:t₀≤t:=by dsimp [t₀,t];exact div_le_div_of_nonneg_right hslo hmR.le
  have hPA:0<pA0:=by dsimp [pA0];positivity
  have hPA1:pA0≤1/2:=by
    have hh:=mul_le_mul hρ₀1 hsstar1 hsstar.le (by norm_num:(0:ℝ)≤1)
    dsimp [pA0];linarith
  obtain ⟨hp0,hp0p,hp0k,_,_,_,_,_,_⟩:=marked_seed_density_bounds m hm ρ s ρ₀ sstar hρ₀ hsstar hρlo hρhi hslo hshi
  have hkform:k=ρ*t/2:=by dsimp [k,p,t];field_simp <;> ring
  have hpform:p=ρ*m*t/2:=by dsimp [p,t];field_simp <;> ring
  have hp0t:p0≤t:=by
    have hk_t:k≤t:=by rw [hkform];nlinarith [mul_nonneg (sub_nonneg.mpr hρhi) (show 0≤t by dsimp [t];positivity)]
    exact hp0k.trans hk_t
  have hPAp:pA0≤p:=by dsimp [pA0,p];linarith
  have hp01:p0≤1/2:=by
    have hh:=mul_le_mul_of_nonneg_right hp0t (show (0:ℝ)≤1 by norm_num)
    dsimp [t] at hh
    have htbound:s/(m:ℝ)≤1/100:=by apply (div_le_iff₀ hmR).mpr;nlinarith
    linarith
  have hp0ref:p0/2≤ρ₀*t₀/4:=by dsimp [p0,t₀];field_simp <;> ring_nf <;> norm_num
  have htUpper:(m:ℝ)*t≤1:=by dsimp [t];field_simp;linarith
  refine ⟨hρ₀,hρ₀1,ht₀,ht₀1,htle,hPA,hPA1,hp0,hp01,hp0p,hp0k,hp0t,?_,?_,?_,hp0ref,htUpper⟩
  · rw [←hpform];exact hPAp
  · rw [←hpform];exact hp0p
  · rw [←hkform];exact hp0k
end Oberwolfach
