module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! Quantities fixed before the host graph for the selected reference colour. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_preparation_reference_densities (m:ℕ) (hm:1≤m) (ρ₀ ρ s:ℝ)
    (hρ₀:0<ρ₀) (hρ:ρ₀≤ρ) (hs:0<s) (hs1:s≤1):
    let t:=s/(m:ℝ)
    let p:=ρ*s/2
    let k:=p/(m:ℝ)
    let kstar:=ρ₀*t/4;
    0<t ∧ t≤s ∧ 0<kstar ∧ kstar≤p ∧ kstar≤k ∧ kstar≤ρ₀*t/4:=by
  intro t p k kstar
  have hmR:(1:ℝ)≤m:=by exact_mod_cast hm
  have hm0:(0:ℝ)<m:=by linarith
  have hρpos:0<ρ:=hρ₀.trans_le hρ
  have ht:0<t:=by dsimp [t];positivity
  have hts:t≤s:=by
    dsimp [t]
    exact div_le_self hs.le hmR
  have hkstar:0<kstar:=by dsimp [kstar];positivity
  have hprods:ρ₀*s≤ρ*s:=mul_le_mul_of_nonneg_right hρ hs.le
  have hksk:kstar≤k:=by
    dsimp [kstar,k,p,t]
    have hnum:ρ₀*s/4≤ρ*s/2:=by nlinarith
    have hh:=div_le_div_of_nonneg_right hnum hm0.le
    convert hh using 1 <;> ring
  have hkp:k≤p:=by
    dsimp [k]
    exact div_le_self (by dsimp [p];positivity) hmR
  exact ⟨ht,hts,hkstar,hksk.trans hkp,hksk,le_rfl⟩
end Oberwolfach
