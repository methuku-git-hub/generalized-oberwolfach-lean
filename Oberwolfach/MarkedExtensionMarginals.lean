module

public import Oberwolfach.MarkedSeedDensities

@[expose] public section

/-! The supplied marked probabilities have a common positive lower bound
depending only on the fixed density lower bounds and the cycle length. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_extension_marginal_lower (m : ℕ) (hm : 1≤m)
    (ρ s ρ₀ s₀ : ℝ) (hρ₀ : 0<ρ₀) (hs₀ : 0<s₀)
    (hρ : ρ₀≤ρ) (hρ1 : ρ≤1) (hs : s₀≤s) (hs1 : s≤1) :
    let pstar:=ρ₀*s₀/(2*m)
    let p:=ρ*s/2
    let k:=p/m
    let t:=s/m
    0<pstar ∧ pstar≤1 ∧ pstar≤p ∧ pstar≤k ∧ pstar≤s ∧ pstar≤t := by
  intro pstar p k t
  have hm1 : (1:ℝ)≤m := by exact_mod_cast hm
  have hmpos : (0:ℝ)<m := by linarith only [hm1]
  have hρpos : 0<ρ := hρ₀.trans_le hρ
  have hspos : 0<s := hs₀.trans_le hs
  have hpstar : 0<pstar := by dsimp [pstar];positivity
  have hp : 0<p := by dsimp [p];positivity
  have hprod:=mul_le_mul hρ hs hs₀.le hρpos.le
  have hklo : pstar≤k := by
    dsimp [pstar,k,p]
    rw [div_div]
    exact div_le_div_of_nonneg_right hprod (by positivity)
  have hkp : k≤p := by
    dsimp [k]
    apply (div_le_iff₀ hmpos).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hm1 hp.le]
  have hps : p≤s := by
    dsimp [p]
    nlinarith only [mul_le_mul_of_nonneg_right hρ1 hspos.le,hspos.le]
  have hkt : k≤t := div_le_div_of_nonneg_right hps hmpos.le
  exact ⟨hpstar,(hklo.trans hkp).trans (hps.trans hs1),hklo.trans hkp,hklo,
    (hklo.trans hkp).trans hps,hklo.trans hkt⟩

end Oberwolfach
