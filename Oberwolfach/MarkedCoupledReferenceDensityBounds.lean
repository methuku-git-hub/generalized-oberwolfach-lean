module

public import Oberwolfach.MarkedSeedDensities
public import Oberwolfach.MarkedSampleReferenceDensityIdentities

@[expose] public section

/-! The lower bounds chosen before the random graph are compatible with
both the sampled-event densities and the reference-level cover-down inputs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_coupled_reference_density_bounds
    (m:ℕ) (hm:1≤m) (ρ₀ sstar ρ s:ℝ)
    (hρ₀:0<ρ₀) (hρ₀1:ρ₀≤1) (hsstar:0<sstar) (hsstar1:sstar≤1/100)
    (hρlo:ρ₀≤ρ) (hρhi:ρ≤1) (hslo:sstar≤s) (hshi:s≤1/100):
    let t₀:=sstar/m
    let t:=s/m
    let pA0:=ρ₀*sstar/2
    let p0:=ρ₀*sstar/(2*m)
    let p:=ρ*s/2
    let k:=p/m;
    0<t₀ ∧ t₀≤1 ∧ 0<pA0 ∧ pA0≤1/2 ∧ 0<p0 ∧ p0≤1/2 ∧
    t₀≤t ∧ (m:ℝ)*t≤1 ∧ pA0≤ρ*(m:ℝ)*t/2 ∧
    p0≤ρ*(m:ℝ)*t/2 ∧ p0≤ρ*t/2 ∧ p0≤t ∧
    p0=ρ₀*t₀/2 ∧ p=ρ*(m:ℝ)*t/2 ∧ k=ρ*t/2 ∧ p0/2=ρ₀*t₀/4 := by
  intro t₀ t pA0 p0 p k
  have hm1:(1:ℝ)≤m := by exact_mod_cast hm
  have hmpos:(0:ℝ)<m := by linarith
  have hm0:(m:ℝ)≠0 := ne_of_gt hmpos
  have hρ:0<ρ := lt_of_lt_of_le hρ₀ hρlo
  have hs:0<s := lt_of_lt_of_le hsstar hslo
  have hprod:ρ₀*sstar≤ρ*s := mul_le_mul hρlo hslo hsstar.le hρ.le
  have ht0:0<t₀ := by dsimp [t₀];positivity
  have ht:0<t := by dsimp [t];positivity
  have hts:t₀≤t := by dsimp [t₀,t];exact div_le_div_of_nonneg_right hslo hmpos.le
  have ht1:t≤1 := by dsimp [t];apply (div_le_iff₀ hmpos).mpr;linarith
  have ht01:t₀≤1 := hts.trans ht1
  have hPA:0<pA0 := by dsimp [pA0];positivity
  have hPA1:pA0≤1/2 := by
    dsimp [pA0]
    have hh:=mul_le_mul_of_nonneg_right hρ₀1 hsstar.le
    nlinarith
  have hp0:0<p0 := by dsimp [p0];positivity
  have hp0pa:p0≤pA0 := by
    dsimp [p0,pA0]
    apply (div_le_iff₀ (by positivity : 0<2*(m:ℝ))).mpr
    nlinarith [mul_nonneg hρ₀.le hsstar.le]
  have hp01:p0≤1/2 := hp0pa.trans hPA1
  have hmt:(m:ℝ)*t=s := by dsimp [t];field_simp
  have hmt1:(m:ℝ)*t≤1 := by rw [hmt];linarith
  have hpap:pA0≤p := by dsimp [pA0,p];linarith
  have hp0k:p0≤k := by
    dsimp [p0,k,p]
    rw [div_div]
    exact div_le_div_of_nonneg_right hprod (by positivity)
  have hkt:k≤t := by
    dsimp [k,p,t]
    apply div_le_div_of_nonneg_right _ hmpos.le
    nlinarith [mul_le_mul_of_nonneg_right hρhi hs.le]
  have ids:=marked_sample_reference_density_identities m (by omega) ρ s ρ₀ sstar
  change p0=ρ₀*t₀/2 ∧ p=ρ*(m:ℝ)*t/2 ∧ k=ρ*t/2 ∧ p0/2=ρ₀*t₀/4 at ids
  refine ⟨ht0,ht01,hPA,hPA1,hp0,hp01,hts,hmt1,?_,?_,?_,hp0k.trans hkt,ids⟩
  · rw [←ids.2.1];exact hpap
  · rw [←ids.2.1];exact hp0pa.trans hpap
  · rw [←ids.2.2.1];exact hp0k
end Oberwolfach
