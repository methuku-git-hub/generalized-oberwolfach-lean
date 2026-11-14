module

public import Mathlib.Tactic

@[expose] public section

/-! The actual density identities used by the marked completion sample.
All constants here depend on the supplied lower density bounds and cycle length. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach

theorem marked_seed_density_bounds (m : ℕ) (hm : 1≤m)
    (ρ s ρstar sstar : ℝ) (hρstar : 0<ρstar) (hsstar : 0<sstar)
    (hρlo : ρstar≤ρ) (hρhi : ρ≤1) (hslo : sstar≤s) (hshi : s≤1/100) :
    let p := ρ*s/2
    let k := p/m
    let t := s/m
    let pstar := ρstar*sstar/(2*m)
    0<pstar ∧ pstar≤p ∧ pstar≤k ∧ pstar≤s ∧
      p≤1 ∧ k≤1 ∧ s≤1 ∧ 0<t ∧ 2*p+2*k≤1 := by
  intro p k t pstar
  have hm' : (1:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hρ : 0<ρ := hρstar.trans_le hρlo
  have hs : 0<s := hsstar.trans_le hslo
  have hp0 : 0<p := by dsimp [p];positivity
  have hprod : ρstar*sstar≤ρ*s := mul_le_mul hρlo hslo hsstar.le hρ.le
  have hklo : pstar≤k := by
    dsimp [pstar,k,p]
    rw [div_div]
    exact div_le_div_of_nonneg_right hprod (by positivity)
  have hkp : k≤p := by dsimp [k];apply (div_le_iff₀ hm0).mpr;nlinarith
  have hps : p≤s := by dsimp [p];nlinarith [mul_le_mul_of_nonneg_right hρhi hs.le]
  have hpp : 0<pstar := by dsimp [pstar];positivity
  refine ⟨hpp,hklo.trans hkp,hklo,(hklo.trans hkp).trans hps,?_,?_,?_,?_,?_⟩
  · linarith
  · linarith
  · linarith
  · dsimp [t];positivity
  · linarith

theorem marked_seed_density_balance (m : ℕ) (hm : 0<m) (ρ s b : ℝ) (hρ : ρ≠0) :
    b*(s/m)=(2*b/ρ)*((ρ*s/2)/m) ∧
      b*(s/m)*m=(2*b/ρ)*(ρ*s/2) := by
  have hm' : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  constructor <;> field_simp <;> ring

end Oberwolfach
