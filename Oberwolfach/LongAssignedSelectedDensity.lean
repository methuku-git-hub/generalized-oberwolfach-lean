module

public import Oberwolfach.LongPreparationUniformSeedDensity
public import Mathlib.Tactic

@[expose] public section
/-! Fixed positive lower bounds for the two selected marked-class rim
probabilities.  The lower bounds depend on the density floor, not on the
actual class density. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_assigned_selected_density_uniform (m:ℕ) (hm:7≤m)
    (ρ₀ ρ:ℝ) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1):
    let s:ℝ:=1/100
    let t:ℝ:=s/m
    let p:ℝ:=ρ*s/2
    let k:ℝ:=ρ*t/2
    let kstar:ℝ:=ρ₀*t/2
    let pstarRef:ℝ:=ρ₀*t/8;
    0<s ∧ s≤1/100 ∧ 0<t ∧ t≤s ∧ t≤1 ∧
    0<kstar ∧ kstar≤p ∧ kstar≤k ∧
    0<pstarRef ∧ pstarRef≤ρ₀*t/4 ∧ k=p/m ∧
    0≤p ∧ 0≤k ∧ 2*p+2*k≤ρ :=by
  intro s t p k kstar pstarRef
  have hmpos:(0:ℝ)<m:=by exact_mod_cast (show 0<m by omega)
  have hmone:(1:ℝ)≤m:=by exact_mod_cast (show 1≤m by omega)
  have hrho:0<ρ:=hρ₀.trans_le hρlo
  have hs:0<s:=by dsimp [s];norm_num
  have ht:0<t:=by dsimp [t];positivity
  have hts:t≤s:=by
    dsimp [t]
    exact (div_le_iff₀ hmpos).2 (by nlinarith)
  have ht1:t≤1:=by dsimp [s] at hts;linarith
  have hk0:0<kstar:=by dsimp [kstar];positivity
  have hkp:kstar≤p:=by
    have h₁:=mul_le_mul_of_nonneg_right hρlo ht.le
    have h₂:=mul_le_mul_of_nonneg_left hts hrho.le
    dsimp [kstar,p]
    exact div_le_div_of_nonneg_right (h₁.trans h₂) (by norm_num)
  have hkk:kstar≤k:=by dsimp [kstar,k];nlinarith
  have hRef:0<pstarRef:=by dsimp [pstarRef];positivity
  have hRefU:pstarRef≤ρ₀*t/4:=by dsimp [pstarRef];nlinarith
  have heq:k=p/m:=by dsimp [k,p,t];ring
  have hp:0≤p:=by dsimp [p];positivity
  have hk:0≤k:=by dsimp [k];positivity
  have hsum:2*p+2*k≤ρ:=by
    dsimp [p,k,s] at *
    nlinarith
  exact ⟨hs,le_rfl,ht,hts,ht1,hk0,hkp,hkk,hRef,hRefU,heq,hp,hk,hsum⟩
end Oberwolfach
